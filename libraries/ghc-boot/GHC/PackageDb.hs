{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  GHC.PackageDb
-- Copyright   :  (c) The University of Glasgow 2009, Duncan Coutts 2014
--
-- Maintainer  :  ghc-devs@haskell.org
-- Portability :  portable
--
-- This module provides the view of GHC's database of registered packages that
-- is shared between GHC the compiler\/library, and the ghc-pkg program. It
-- defines the database format that is shared between GHC and ghc-pkg.
--
-- The database format, and this library are constructed so that GHC does not
-- have to depend on the Cabal library. The ghc-pkg program acts as the
-- gateway between the external package format (which is defined by Cabal) and
-- the internal package format which is specialised just for GHC.
--
-- GHC the compiler only needs some of the information which is kept about
-- registerd packages, such as module names, various paths etc. On the other
-- hand ghc-pkg has to keep all the information from Cabal packages and be able
-- to regurgitate it for users and other tools.
--
-- The first trick is that we duplicate some of the information in the package
-- database. We essentially keep two versions of the datbase in one file, one
-- version used only by ghc-pkg which keeps the full information (using the
-- serialised form of the 'InstalledPackageInfo' type defined by the Cabal
-- library); and a second version written by ghc-pkg and read by GHC which has
-- just the subset of information that GHC needs.
--
-- The second trick is that this module only defines in detail the format of
-- the second version -- the bit GHC uses -- and the part managed by ghc-pkg
-- is kept in the file but here we treat it as an opaque blob of data. That way
-- this library avoids depending on Cabal.
--
module GHC.PackageDb (
       InstalledPackageInfo(..),
       DbModule(..),
       DbUnitId(..),
       BinaryStringRep(..),
       DbUnitIdModuleRep(..),
       emptyInstalledPackageInfo,
       readPackageDbForGhc,
       readPackageDbForGhcPkg,
       writePackageDb
  ) where

import Data.Version (Version(..))
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BS.Char8
import qualified Data.ByteString.Lazy as BS.Lazy
import qualified Data.ByteString.Lazy.Internal as BS.Lazy (defaultChunkSize)
import Data.Binary as Bin
import Data.Binary.Put as Bin
import Data.Binary.Get as Bin
import Control.Exception as Exception
import Control.Monad (when)
import System.FilePath
import System.IO
import System.IO.Error
import GHC.IO.Exception (IOErrorType(InappropriateType))
import System.Directory


-- | This is a subset of Cabal's 'InstalledPackageInfo', with just the bits
-- that GHC is interested in.
--
data InstalledPackageInfo compid srcpkgid srcpkgname instunitid unitid modulename mod
   = InstalledPackageInfo {
       unitId             :: instunitid,
       componentId        :: compid,
       instantiatedWith   :: [(modulename, mod)],
       sourcePackageId    :: srcpkgid,
       packageName        :: srcpkgname,
       packageVersion     :: Version,
       abiHash            :: String,
       depends            :: [instunitid],
       importDirs         :: [FilePath],
       hsLibraries        :: [String],
       extraLibraries     :: [String],
       extraGHCiLibraries :: [String],
       libraryDirs        :: [FilePath],
       frameworks         :: [String],
       frameworkDirs      :: [FilePath],
       ldOptions          :: [String],
       ccOptions          :: [String],
       includes           :: [String],
       includeDirs        :: [FilePath],
       haddockInterfaces  :: [FilePath],
       haddockHTMLs       :: [FilePath],
       exposedModules     :: [(modulename, Maybe mod)],
       hiddenModules      :: [modulename],
       indefinite         :: Bool,
       exposed            :: Bool,
       trusted            :: Bool
     }
  deriving (Eq, Show)

-- | A convenience constraint synonym for common constraints over parameters
-- to 'InstalledPackageInfo'.
type RepInstalledPackageInfo compid srcpkgid srcpkgname instunitid unitid modulename mod =
    (BinaryStringRep srcpkgid, BinaryStringRep srcpkgname,
     BinaryStringRep modulename, BinaryStringRep compid,
     BinaryStringRep instunitid,
     DbUnitIdModuleRep instunitid compid unitid modulename mod)

-- | A type-class for the types which can be converted into 'DbModule'/'DbUnitId'.
-- There is only one type class because these types are mutually recursive.
-- NB: The functional dependency helps out type inference in cases
-- where types would be ambiguous.
class DbUnitIdModuleRep instunitid compid unitid modulename mod
    | mod -> unitid, unitid -> mod, mod -> modulename, unitid -> compid, unitid -> instunitid
    where
  fromDbModule :: DbModule instunitid compid unitid modulename mod -> mod
  toDbModule :: mod -> DbModule instunitid compid unitid modulename mod
  fromDbUnitId :: DbUnitId instunitid compid unitid modulename mod -> unitid
  toDbUnitId :: unitid -> DbUnitId instunitid compid unitid modulename mod

-- | @ghc-boot@'s copy of 'Module', i.e. what is serialized to the database.
-- Use 'DbUnitIdModuleRep' to convert it into an actual 'Module'.
-- It has phantom type parameters as this is the most convenient way
-- to avoid undecidable instances.
data DbModule instunitid compid unitid modulename mod
   = DbModule {
       dbModuleUnitId :: unitid,
       dbModuleName :: modulename
     }
   | DbModuleVar {
       dbModuleVarName :: modulename
     }
  deriving (Eq, Show)

-- | @ghc-boot@'s copy of 'UnitId', i.e. what is serialized to the database.
-- Use 'DbUnitIdModuleRep' to convert it into an actual 'UnitId'.
-- It has phantom type parameters as this is the most convenient way
-- to avoid undecidable instances.
data DbUnitId instunitid compid unitid modulename mod
   = DbUnitId compid [(modulename, mod)]
   | DbInstalledUnitId instunitid
  deriving (Eq, Show)

class BinaryStringRep a where
  fromStringRep :: BS.ByteString -> a
  toStringRep   :: a -> BS.ByteString

emptyInstalledPackageInfo :: RepInstalledPackageInfo a b c d e f g
                          => InstalledPackageInfo a b c d e f g
emptyInstalledPackageInfo =
  InstalledPackageInfo {
       unitId             = fromStringRep BS.empty,
       componentId        = fromStringRep BS.empty,
       instantiatedWith   = [],
       sourcePackageId    = fromStringRep BS.empty,
       packageName        = fromStringRep BS.empty,
       packageVersion     = Version [] [],
       abiHash            = "",
       depends            = [],
       importDirs         = [],
       hsLibraries        = [],
       extraLibraries     = [],
       extraGHCiLibraries = [],
       libraryDirs        = [],
       frameworks         = [],
       frameworkDirs      = [],
       ldOptions          = [],
       ccOptions          = [],
       includes           = [],
       includeDirs        = [],
       haddockInterfaces  = [],
       haddockHTMLs       = [],
       exposedModules     = [],
       hiddenModules      = [],
       indefinite         = False,
       exposed            = False,
       trusted            = False
  }

-- | Read the part of the package DB that GHC is interested in.
--
readPackageDbForGhc :: RepInstalledPackageInfo a b c d e f g =>
                       FilePath -> IO [InstalledPackageInfo a b c d e f g]
readPackageDbForGhc file =
    decodeFromFile file getDbForGhc
  where
    getDbForGhc = do
      _version    <- getHeader
      _ghcPartLen <- get :: Get Word32
      ghcPart     <- get
      -- the next part is for ghc-pkg, but we stop here.
      return ghcPart

-- | Read the part of the package DB that ghc-pkg is interested in
--
-- Note that the Binary instance for ghc-pkg's representation of packages
-- is not defined in this package. This is because ghc-pkg uses Cabal types
-- (and Binary instances for these) which this package does not depend on.
--
readPackageDbForGhcPkg :: Binary pkgs => FilePath -> IO pkgs
readPackageDbForGhcPkg file =
    decodeFromFile file getDbForGhcPkg
  where
    getDbForGhcPkg = do
      _version    <- getHeader
      -- skip over the ghc part
      ghcPartLen  <- get :: Get Word32
      _ghcPart    <- skip (fromIntegral ghcPartLen)
      -- the next part is for ghc-pkg
      ghcPkgPart  <- get
      return ghcPkgPart

-- | Write the whole of the package DB, both parts.
--
writePackageDb :: (Binary pkgs, RepInstalledPackageInfo a b c d e f g) =>
                  FilePath -> [InstalledPackageInfo a b c d e f g] -> pkgs -> IO ()
writePackageDb file ghcPkgs ghcPkgPart =
    writeFileAtomic file (runPut putDbForGhcPkg)
  where
    putDbForGhcPkg = do
        putHeader
        put               ghcPartLen
        putLazyByteString ghcPart
        put               ghcPkgPart
      where
        ghcPartLen :: Word32
        ghcPartLen = fromIntegral (BS.Lazy.length ghcPart)
        ghcPart    = encode ghcPkgs

getHeader :: Get (Word32, Word32)
getHeader = do
    magic <- getByteString (BS.length headerMagic)
    when (magic /= headerMagic) $
      fail "not a ghc-pkg db file, wrong file magic number"

    majorVersion <- get :: Get Word32
    -- The major version is for incompatible changes

    minorVersion <- get :: Get Word32
    -- The minor version is for compatible extensions

    when (majorVersion /= 1) $
      fail "unsupported ghc-pkg db format version"
    -- If we ever support multiple major versions then we'll have to change
    -- this code

    -- The header can be extended without incrementing the major version,
    -- we ignore fields we don't know about (currently all).
    headerExtraLen <- get :: Get Word32
    skip (fromIntegral headerExtraLen)

    return (majorVersion, minorVersion)

putHeader :: Put
putHeader = do
    putByteString headerMagic
    put majorVersion
    put minorVersion
    put headerExtraLen
  where
    majorVersion   = 1 :: Word32
    minorVersion   = 0 :: Word32
    headerExtraLen = 0 :: Word32

headerMagic :: BS.ByteString
headerMagic = BS.Char8.pack "\0ghcpkg\0"


-- TODO: we may be able to replace the following with utils from the binary
-- package in future.

-- | Feed a 'Get' decoder with data chunks from a file.
--
decodeFromFile :: FilePath -> Get a -> IO a
decodeFromFile file decoder =
    withBinaryFile file ReadMode $ \hnd ->
      feed hnd (runGetIncremental decoder)
  where
    feed hnd (Partial k)  = do chunk <- BS.hGet hnd BS.Lazy.defaultChunkSize
                               if BS.null chunk
                                 then feed hnd (k Nothing)
                                 else feed hnd (k (Just chunk))
    feed _ (Done _ _ res) = return res
    feed _ (Fail _ _ msg) = ioError err
      where
        err = mkIOError InappropriateType loc Nothing (Just file)
              `ioeSetErrorString` msg
        loc = "GHC.PackageDb.readPackageDb"

-- Copied from Cabal's Distribution.Simple.Utils.
writeFileAtomic :: FilePath -> BS.Lazy.ByteString -> IO ()
writeFileAtomic targetPath content = do
  let (targetDir, targetFile) = splitFileName targetPath
  Exception.bracketOnError
    (openBinaryTempFileWithDefaultPermissions targetDir $ targetFile <.> "tmp")
    (\(tmpPath, handle) -> hClose handle >> removeFile tmpPath)
    (\(tmpPath, handle) -> do
        BS.Lazy.hPut handle content
        hClose handle
        renameFile tmpPath targetPath)

instance (RepInstalledPackageInfo a b c d e f g) =>
         Binary (InstalledPackageInfo a b c d e f g) where
  put (InstalledPackageInfo
         unitId componentId instantiatedWith sourcePackageId
         packageName packageVersion
         abiHash depends importDirs
         hsLibraries extraLibraries extraGHCiLibraries libraryDirs
         frameworks frameworkDirs
         ldOptions ccOptions
         includes includeDirs
         haddockInterfaces haddockHTMLs
         exposedModules hiddenModules
         indefinite exposed trusted) = do
    put (toStringRep sourcePackageId)
    put (toStringRep packageName)
    put packageVersion
    put (toStringRep unitId)
    put (toStringRep componentId)
    put (map (\(mod_name, mod) -> (toStringRep mod_name, toDbModule mod))
             instantiatedWith)
    put abiHash
    put (map toStringRep depends)
    put importDirs
    put hsLibraries
    put extraLibraries
    put extraGHCiLibraries
    put libraryDirs
    put frameworks
    put frameworkDirs
    put ldOptions
    put ccOptions
    put includes
    put includeDirs
    put haddockInterfaces
    put haddockHTMLs
    put (map (\(mod_name, mb_mod) -> (toStringRep mod_name, fmap toDbModule mb_mod))
             exposedModules)
    put (map toStringRep hiddenModules)
    put indefinite
    put exposed
    put trusted

  get = do
    sourcePackageId    <- get
    packageName        <- get
    packageVersion     <- get
    unitId             <- get
    componentId        <- get
    instantiatedWith   <- get
    abiHash            <- get
    depends            <- get
    importDirs         <- get
    hsLibraries        <- get
    extraLibraries     <- get
    extraGHCiLibraries <- get
    libraryDirs        <- get
    frameworks         <- get
    frameworkDirs      <- get
    ldOptions          <- get
    ccOptions          <- get
    includes           <- get
    includeDirs        <- get
    haddockInterfaces  <- get
    haddockHTMLs       <- get
    exposedModules     <- get
    hiddenModules      <- get
    indefinite         <- get
    exposed            <- get
    trusted            <- get
    return (InstalledPackageInfo
              (fromStringRep unitId)
              (fromStringRep componentId)
              (map (\(mod_name, mod) -> (fromStringRep mod_name, fromDbModule mod))
                instantiatedWith)
              (fromStringRep sourcePackageId)
              (fromStringRep packageName) packageVersion
              abiHash
              (map fromStringRep depends)
              importDirs
              hsLibraries extraLibraries extraGHCiLibraries libraryDirs
              frameworks frameworkDirs
              ldOptions ccOptions
              includes includeDirs
              haddockInterfaces haddockHTMLs
              (map (\(mod_name, mb_mod) ->
                        (fromStringRep mod_name, fmap fromDbModule mb_mod))
                   exposedModules)
              (map fromStringRep hiddenModules)
              indefinite exposed trusted)

instance (BinaryStringRep modulename, BinaryStringRep compid,
          BinaryStringRep instunitid,
          DbUnitIdModuleRep instunitid compid unitid modulename mod) =>
         Binary (DbModule instunitid compid unitid modulename mod) where
  put (DbModule dbModuleUnitId dbModuleName) = do
    putWord8 0
    put (toDbUnitId dbModuleUnitId)
    put (toStringRep dbModuleName)
  put (DbModuleVar dbModuleVarName) = do
    putWord8 1
    put (toStringRep dbModuleVarName)
  get = do
    b <- getWord8
    case b of
      0 -> do dbModuleUnitId <- get
              dbModuleName <- get
              return (DbModule (fromDbUnitId dbModuleUnitId)
                               (fromStringRep dbModuleName))
      _ -> do dbModuleVarName <- get
              return (DbModuleVar (fromStringRep dbModuleVarName))

instance (BinaryStringRep modulename, BinaryStringRep compid,
          BinaryStringRep instunitid,
          DbUnitIdModuleRep instunitid compid unitid modulename mod) =>
         Binary (DbUnitId instunitid compid unitid modulename mod) where
  put (DbInstalledUnitId instunitid) = do
    putWord8 0
    put (toStringRep instunitid)
  put (DbUnitId dbUnitIdComponentId dbUnitIdInsts) = do
    putWord8 1
    put (toStringRep dbUnitIdComponentId)
    put (map (\(mod_name, mod) -> (toStringRep mod_name, toDbModule mod)) dbUnitIdInsts)
  get = do
    b <- getWord8
    case b of
      0 -> do
        instunitid <- get
        return (DbInstalledUnitId (fromStringRep instunitid))
      _ -> do
        dbUnitIdComponentId <- get
        dbUnitIdInsts <- get
        return (DbUnitId
            (fromStringRep dbUnitIdComponentId)
            (map (\(mod_name, mod) -> ( fromStringRep mod_name
                                      , fromDbModule mod))
                 dbUnitIdInsts))
