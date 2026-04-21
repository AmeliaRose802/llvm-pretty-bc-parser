{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE ViewPatterns #-}

module Data.LLVM.BitCode.IR.Module where

import Data.LLVM.BitCode.Bitstream
import Data.LLVM.BitCode.IR.Attrs
import Data.LLVM.BitCode.IR.Blocks
import Data.LLVM.BitCode.IR.Constants
import Data.LLVM.BitCode.IR.Function
import Data.LLVM.BitCode.IR.Globals
import Data.LLVM.BitCode.IR.Metadata
import Data.LLVM.BitCode.IR.Types
import Data.LLVM.BitCode.IR.Values
import Data.LLVM.BitCode.Match
import Data.LLVM.BitCode.Parse
import Data.LLVM.BitCode.Record
import Text.LLVM.AST
import Text.LLVM.Triple.AST (TargetTriple)
import Text.LLVM.Triple.Parse (parseTriple)

import qualified Codec.Binary.UTF8.String as UTF8 (decode)
import Control.Monad (foldM,guard,when,forM_)
import Data.List (sortOn)
import Data.Word (Word64)
import qualified Data.Foldable as F
import qualified Data.Map as Map
import qualified Data.Sequence as Seq
import Data.Sequence (Seq)
import qualified Data.Traversable as T


-- Module Block Parsing --------------------------------------------------------

data PartialModule = PartialModule
  { partialGlobalIx   :: !Int
  , partialGlobals    :: GlobalList
  , partialDefines    :: DefineList
  , partialDeclares   :: DeclareList
  , partialTriple     :: TargetTriple
  , partialDataLayout :: DataLayout
  , partialInlineAsm  :: InlineAsm
  , partialComdat     :: !(Seq (String,SelectionKind))
  , partialAliasIx    :: !Int
  , partialAliases    :: AliasList
  , partialNamedMd    :: !(Seq NamedMd)
  , partialUnnamedMd  :: !(Seq PartialUnnamedMd)
  , partialSections   :: !(Seq String)
  , partialSourceName :: !(Maybe String)
  }

emptyPartialModule :: PartialModule
emptyPartialModule  = PartialModule
  { partialGlobalIx   = 0
  , partialGlobals    = mempty
  , partialDefines    = mempty
  , partialDeclares   = mempty
  , partialTriple     = mempty
  , partialDataLayout = mempty
  , partialInlineAsm  = mempty
  , partialAliasIx    = 0
  , partialAliases    = mempty
  , partialNamedMd    = mempty
  , partialUnnamedMd  = mempty
  , partialSections   = mempty
  , partialSourceName = mempty
  , partialComdat     = mempty
  }

-- | Fixup the global variables and declarations, and return the completed
-- module.
finalizeModule :: PartialModule -> Parse Module
finalizeModule pm = label "finalizeModule" $ do
  types    <- resolveTypeDecls
  let defs = Map.fromList [ (partialName d, partialSymtab d)
                          | d <- F.toList (partialDefines pm) ]
  defines <- T.mapM (finalizePartialDefine defs) (partialDefines pm)
  liftFinalize defs $ do
    globals  <- T.mapM finalizeGlobal (partialGlobals pm)
    declares <- T.mapM finalizeDeclare (partialDeclares pm)
    aliases  <- T.mapM finalizePartialAlias (partialAliases pm)
    unnamed  <- T.mapM finalizePartialUnnamedMd (dedupMetadata (partialUnnamedMd pm))
    return emptyModule
      { modSourceName = partialSourceName pm
      , modTriple     = partialTriple pm
      , modDataLayout = partialDataLayout pm
      , modNamedMd    = F.toList (partialNamedMd pm)
      , modUnnamedMd  = sortOn umIndex (F.toList unnamed)
      , modGlobals    = F.toList globals
      , modDefines    = F.toList defines
      , modTypes      = types
      , modDeclares   = F.toList declares
      , modInlineAsm  = partialInlineAsm pm
      , modAliases    = F.toList aliases
      , modComdat     = Map.fromList (F.toList (partialComdat pm))
      }

-- | Parse PARAMATTR and PARAMATTR_GROUP blocks, capturing only the small
-- subset of attributes we care about (e.g., dead_on_return) and skipping the
-- rest.
parseParamAttrTables :: [Entry] -> Parse ()
parseParamAttrTables ents = forM_ ents $ \e ->
  case e of
    (paramattrGroupBlockId -> Just es) -> parseParamAttrGroupBlock es
    (paramattrBlockId      -> Just es) -> parseParamAttrBlock es
    _ -> pure ()

parseParamAttrBlock :: [Entry] -> Parse ()
parseParamAttrBlock ents = label "PARAMATTR_BLOCK" $
  forM_ ents $ \e ->
    case e of
      (fromEntry -> Just r) ->
        case recordCode r of
          -- PARAMATTR_CODE_ENTRY: [attrgrp0, attrgrp1, ...]
          2 -> do
            gids <- parseFields r 0 (numeric :: Match Field Int)
            addParamAttrList gids
          -- PARAMATTR_CODE_ENTRY_OLD (deprecated)
          _ -> pure ()
      _ -> pure ()

parseParamAttrGroupBlock :: [Entry] -> Parse ()
parseParamAttrGroupBlock ents = label "PARAMATTR_GROUP_BLOCK" $
  forM_ ents $ \e ->
    case e of
      (fromEntry -> Just r) ->
        case recordCode r of
          -- PARAMATTR_GRP_CODE_ENTRY: [grpid, idx, attr0, attr1, ...]
          3 -> do
            gid <- parseField r 0 (numeric :: Match Field Int)
            idx <- parseField r 1 (numeric :: Match Field Word64)
            attrs <- parseParamAttrs r 2
            addParamAttrGroup gid ParamAttrGroup { pagIndex = idx, pagAttrs = attrs }
          _ -> pure ()
      _ -> pure ()

-- Parse the flat attribute list in a PARAMATTR_GRP_CODE_ENTRY record.
--
-- We only retain dead_on_return (LLVM 22) and dead_on_unwind (LLVM 21) for now.
parseParamAttrs :: Record -> Int -> Parse [ParamAttr]
parseParamAttrs r0 start = go start []
  where
    r = flattenRecord r0
    len = length (recordFields r)

    go i acc
      | i >= len  = pure (reverse acc)
      | otherwise = do
          kind <- parseField r i (numeric :: Match Field Word64)
          case kind of
            -- well-known attribute (no value)
            0 -> do
              key <- parseField r (i+1) (numeric :: Match Field Word64)
              let acc' = case key of
                    91  -> DeadOnUnwind : acc
                    103 -> DeadOnReturn : acc
                    _   -> acc
              go (i+2) acc'
            -- well-known attribute with integer value
            1 -> go (i+3) acc
            -- string attribute
            3 -> do
              j <- skipCString (i+1)
              go j acc
            -- string attribute with string value
            4 -> do
              j <- skipCString (i+1)
              k <- skipCString j
              go k acc
            -- unknown kind code; skip the rest conservatively
            _ -> pure (reverse acc)

    skipCString j
      | j >= len  = pure j
      | otherwise = do
          w <- parseField r j (numeric :: Match Field Word64)
          if w == 0 then pure (j+1) else skipCString (j+1)

-- | Parse an LLVM Module out of the top-level block in a Bitstream.
parseModuleBlock :: [Entry] -> Parse Module
parseModuleBlock ents = label "MODULE_BLOCK" $ do

  -- the explicit type symbol table has been removed in 3.1, so we parse the
  -- type table, and generate the type symbol table from it.
  tsymtab <- label "type symbol table" $ do
    mb <- match (findMatch typeBlockIdNew) ents
    case mb of
      Just es -> parseTypeBlock es
      Nothing -> return mempty

  withTypeSymtab tsymtab $ label "value symbol table" $ do
    -- parse the value symbol table out first, if there is one
    symtab <- do
      mb <- match (findMatch valueSymtabBlockId) ents
      case mb of
        Just es -> parseValueSymbolTableBlock es
        Nothing -> return emptyValueSymtab

    -- LLVM 21+ may store the string table inside the module block.
    -- We need to discover it up-front so that name records that use the string
    -- table can be parsed.
    forM_ ents $ \e ->
      case e of
        (moduleStrtabBlockId -> Just es) ->
          forM_ es $ \e' ->
            case fromEntry e' of
              Just r | recordCode r == 1 -> do
                st <- mkStrtab <$> parseField r 0 fieldBlob
                setStringTable st
              _ -> pure ()
        _ -> pure ()

    -- Parse PARAMATTR / PARAMATTR_GROUP tables up-front so later records that
    -- reference them (e.g., call/callbr/invoke, function declarations) can be
    -- validated without depending on block ordering.
    parseParamAttrTables ents

    pm <- withValueSymtab symtab
        $ foldM parseModuleBlockEntry emptyPartialModule ents

    finalizeModule pm


-- | Parse the entries in a module block.
parseModuleBlockEntry :: PartialModule -> Entry -> Parse PartialModule

parseModuleBlockEntry pm (blockInfoBlockId -> Just _) =
  -- skip the block info block, as we only use it during Bitstream parsing.
  return pm

parseModuleBlockEntry pm (typeBlockIdNew -> Just _) = do
  -- TYPE_BLOCK_ID_NEW
  -- this is skipped, as it's parsed before anything else, in parseModuleBlock
  return pm

parseModuleBlockEntry pm (constantsBlockId -> Just es) = do
  -- CONSTANTS_BLOCK_ID
  parseConstantsBlock es
  return pm

parseModuleBlockEntry pm (moduleCodeFunction -> Just r) = do
  -- MODULE_CODE_FUNCTION
  parseFunProto r pm

parseModuleBlockEntry pm (functionBlockId -> Just es) = label "FUNCTION_BLOCK_ID" $ do
  let maxUnMdIdx = UnnamedMdIdx $ length (partialUnnamedMd pm)
  def <- parseFunctionBlock maxUnMdIdx es
  let def' = def { partialGlobalMd = mempty }
  return pm { partialDefines = partialDefines pm Seq.|> def'
            , partialUnnamedMd = partialGlobalMd def <> partialUnnamedMd pm
            }

parseModuleBlockEntry pm (paramattrBlockId -> Just _) = do
  -- PARAMATTR_BLOCK_ID
  -- TODO: skip for now
  return pm

parseModuleBlockEntry pm (paramattrGroupBlockId -> Just _) = do
  -- PARAMATTR_GROUP_BLOCK_ID
  -- TODO: skip for now
  return pm

parseModuleBlockEntry pm (metadataBlockId -> Just es) = label "METADATA_BLOCK_ID" $ do
  vt <- getValueTable
  let maxUnMdIdx = UnnamedMdIdx $ length (partialUnnamedMd pm)
  (ns,(gs,_),_,_,atts) <- parseMetadataBlock maxUnMdIdx vt es
  return $ addGlobalAttachments atts pm
    { partialNamedMd   = partialNamedMd   pm <> ns
    , partialUnnamedMd = partialUnnamedMd pm <> gs
    }

parseModuleBlockEntry pm (valueSymtabBlockId -> Just _es) = do
  -- VALUE_SYMTAB_BLOCK_ID
  -- NOTE: we parse the value symbol table eagerly at the beginning of the
  -- MODULE_BLOCK
  return pm

parseModuleBlockEntry pm (moduleCodeTriple -> Just r) = do
  -- MODULE_CODE_TRIPLE
  triple <- UTF8.decode <$> parseFields r 0 char
  return (pm { partialTriple = parseTriple triple })

parseModuleBlockEntry pm (moduleCodeDatalayout -> Just r) = do
  -- MODULE_CODE_DATALAYOUT
  layout <- UTF8.decode <$> parseFields r 0 char
  case parseDataLayout layout of
    Nothing -> fail ("unable to parse data layout: ``" ++ layout ++ "''")
    Just dl -> return (pm { partialDataLayout = dl })

parseModuleBlockEntry pm (moduleCodeAsm -> Just r) = do
  -- MODULE_CODE_ASM
  asm <- UTF8.decode <$> parseFields r 0 char
  return pm { partialInlineAsm = lines asm }

parseModuleBlockEntry pm (abbrevDef -> Just _) = do
  -- skip abbreviation definitions
  return pm

parseModuleBlockEntry pm (moduleCodeGlobalvar -> Just r) = do
  -- MODULE_CODE_GLOBALVAR
  pg <- parseGlobalVar (partialGlobalIx pm) r
  return pm
    { partialGlobalIx = succ (partialGlobalIx pm)
    , partialGlobals  = partialGlobals pm Seq.|> pg
    }

parseModuleBlockEntry pm (moduleCodeAlias -> Just r) = label "MODULE_CODE_ALIAS_OLD" $ do
  pa <- parseAliasOld (partialAliasIx pm) r
  return pm
    { partialAliasIx = succ (partialAliasIx pm)
    , partialAliases = partialAliases pm Seq.|> pa
    }

parseModuleBlockEntry pm (moduleCodeVersion -> Just r) = do
  -- MODULE_CODE_VERSION

  -- please see:
  -- http://llvm.org/docs/BitCodeFormat.html#module-code-version-record
  version <- parseField r 0 numeric
  setModVersion version
  case version :: Int of
    0 -> setRelIds False  -- Absolute value ids in LLVM <= 3.2
    1 -> setRelIds True   -- Relative value ids in LLVM >= 3.3
    2 -> setRelIds True   -- Relative value ids in LLVM >= 5.0
    -- LLVM 21+ currently still uses relative value ids, but may bump the
    -- module version id. Accept newer ids conservatively.
    _ -> setRelIds True

  return pm

parseModuleBlockEntry pm (moduleCodeSectionname -> Just r) = do
  name <- UTF8.decode <$> parseFields r 0 char
  return pm { partialSections = partialSections pm Seq.|> name }

parseModuleBlockEntry pm (moduleCodeComdat -> Just r) = do
  -- MODULE_CODE_COMDAT
  when (length (recordFields r) < 2) (fail "Invalid record (MODULE_CODE_COMDAT)")
  -- This was last updated in 0fc96d5, but the implementation appeared a bit
  -- buggy for clang++ 3.8. Since no known downstream consumer uses it, it was
  -- removed.
  return pm

parseModuleBlockEntry pm (moduleCodeVSTOffset -> Just _) = do
  -- MODULE_CODE_VSTOFFSET
  -- TODO: should we handle this?
  return pm

parseModuleBlockEntry pm (moduleCodeAliasNew -> Just r) = label "MODULE_CODE_ALIAS" $ do
  pa <- parseAlias r
  return pm
    { partialAliasIx = succ (partialAliasIx pm)
    , partialAliases = partialAliases pm Seq.|> pa
    }

parseModuleBlockEntry pm (moduleCodeMDValsUnused -> Just _) = do
  -- MODULE_CODE_METADATA_VALUES_UNUSED
  return pm

parseModuleBlockEntry pm (moduleCodeSourceFilename -> Just r) = do
  -- MODULE_CODE_SOURCE_FILENAME
  do str <- parseField r 0 cstring
     return pm { partialSourceName = Just str }

parseModuleBlockEntry pm (moduleCodeHash -> Just _) = do
  -- MODULE_CODE_HASH
  -- It should be safe to ignore this for now.
  --fail "MODULE_CODE_HASH"
  return pm

parseModuleBlockEntry _ (moduleCodeIFunc -> Just _) = do
  -- MODULE_CODE_IFUNC
  fail "MODULE_CODE_IFUNC"

parseModuleBlockEntry pm (uselistBlockId -> Just _) = do
  -- USELIST_BLOCK_ID
  -- XXX ?? fail "USELIST_BLOCK_ID"
  return pm

parseModuleBlockEntry pm (moduleStrtabBlockId -> Just _) = do
  -- MODULE_STRTAB_BLOCK_ID
  -- Parsed eagerly in parseModuleBlock (so name records can resolve symbols).
  return pm

parseModuleBlockEntry pm (globalvalSummaryBlockId -> Just _) = do
  -- GLOBALVAL_SUMMARY_BLOCK_ID
  -- It should be safe to ignore this for now.
  return pm

parseModuleBlockEntry pm (operandBundleTagsBlockId -> Just _) = do
  -- OPERAND_BUNDLE_TAGS_BLOCK_ID
  -- fail "OPERAND_BUNDLE_TAGS_BLOCK_ID"
  return pm

parseModuleBlockEntry pm (metadataKindBlockId -> Just es) = label "METADATA_KIND_BLOCK_ID" $ do
  forM_ es $ \e ->
    case fromEntry e of
      Just r -> parseMetadataKindEntry r
      Nothing -> fail "Can't parse metadata kind block entry."
  return pm

parseModuleBlockEntry pm (strtabBlockId -> Just _) =
  -- Handled already.
  return pm

parseModuleBlockEntry pm (ltoSummaryBlockId -> Just _) =
  -- It should be safe to ignore this for now.
  --label "FULL_LTO_GLOBALVAL_SUMMARY_BLOCK_ID" $ do
  --  fail "FULL_LTO_GLOBALVAL_SUMMARY_BLOCK_ID unsupported"
  return pm

parseModuleBlockEntry pm (symtabBlockId -> Just [symtabBlobId -> Just _]) =
  -- Handled already
  return pm

parseModuleBlockEntry pm (syncScopeNamesBlockId -> Just _) =
  label "SYNC_SCOPE_NAMES_BLOCK_ID" $ do
    -- TODO: record this information somewhere
    return pm

-- New LLVM versions occasionally add optional module sub-blocks. If we don't
-- understand one, skip it rather than failing to parse the whole module.
parseModuleBlockEntry pm (block -> Just _) =
  return pm

parseModuleBlockEntry _ e =
  fail ("unexpected module block entry: " ++ show e)

parseFunProto :: Record -> PartialModule -> Parse PartialModule
parseFunProto r pm = label "FUNCTION" $ do
  ix   <- nextValueId
  (name, offset) <- oldOrStrtabName ix r
  let field i = parseField r (i + offset)
  funTy   <- getType =<< field 0 numeric
  let ty = case funTy of
             PtrTo _  -> funTy
             _        -> PtrTo funTy

  isProto <-             field 2 numeric

  link    <-             field 3 linkage

  -- Validate the referenced parameter attribute list (if present). We do not
  -- currently model function/parameter attributes in the AST, but parsing these
  -- tables ensures LLVM 21+ attributes like dead_on_return don't break parsing.
  when (length (recordFields r) > (4 + offset)) $ do
    pal <- field 4 numeric
    when (pal /= (0 :: Int)) $ do
      mb <- lookupParamAttrList pal
      case mb of
        Nothing -> pure ()
        Just gids -> forM_ gids $ \gid -> do
          _ <- lookupParamAttrGroup gid
          pure ()

  vis     <-             field 7 visibility

  section <-
    if length (recordFields r) >= 6
       then do sid <- field 6 numeric
               if sid == 0
                  then return Nothing
                  else do let sid' = sid - 1
                          when (sid' >= length (partialSections pm))
                              (fail "invalid section name index")
                          return (Just (Seq.index (partialSections pm) sid'))

       else return Nothing

  -- push the function type
  _    <- pushValue (Typed ty (ValSymbol name))
  let lkMb t x
       | length t > x = Just (Seq.index t x)
       | otherwise        = Nothing
  comdat <- if length (recordFields r) >= 12
               then do comdatID <- field 12 numeric
                       pure (fst <$> partialComdat pm `lkMb` comdatID)
               else pure Nothing
  let proto = FunProto
        { protoType  = ty
        , protoLinkage =
          do -- we emit a Nothing here to maintain output compatibility with
             -- llvm-dis when linkage is External
             guard (link /= External)
             return link
        , protoVisibility = Just vis
        , protoGC    = Nothing
        , protoSym   = name
        , protoIndex = ix
        , protoSect  = section
        , protoComdat = comdat
        }

  if isProto == (0 :: Int)
     then pushFunProto proto >> return pm
     else return pm { partialDeclares = partialDeclares pm Seq.|> proto }


addGlobalAttachments :: PGlobalAttachments -> (PartialModule -> PartialModule)
addGlobalAttachments gs0 pm = pm { partialGlobals = go (partialGlobals pm) gs0 }
  where

  go gs atts | Map.null atts = gs

  go gs atts =
    case Seq.viewl gs of
      Seq.EmptyL -> Seq.empty

      g Seq.:< gs' ->
        let (mb,atts') = Map.updateLookupWithKey (\_ _ -> Nothing) (pgSym g) atts
         in case mb of
              Just md -> g { pgMd = md } Seq.<| go gs' atts'
              Nothing -> g               Seq.<| go gs' atts'
