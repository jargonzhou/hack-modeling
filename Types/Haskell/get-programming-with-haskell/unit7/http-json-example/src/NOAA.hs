module NOAA
(
    NOAAResponse
    ,metadata
    ,results
    ,noaaFromJson
    ,printResults
) where

import qualified Data.ByteString.Lazy.Char8 as LC
import           Data.Text                  as T (Text, pack)

import           Control.Monad              (forM_)
import           Data.Aeson                 (FromJSON (parseJSON),
                                             Value (Object), decode, (.:))
import           Data.Aeson.Types           (prependFailure, typeMismatch)
import           GHC.Generics               (Generic)



data NOAAResult = NOAAResult
    {
    uid            :: T.Text
    , mindate      :: T.Text
    , maxdate      :: T.Text
    , name         :: T.Text
    , datacoverage :: Float -- float: 0.25
    , resultId     :: T.Text -- id
    } deriving Show

instance FromJSON NOAAResult where
    parseJSON (Object v) =
        NOAAResult <$> v .: "uid"
            <*> v .: "mindate"
            <*> v .: "maxdate"
            <*> v .: "name"
            <*> v .: "datacoverage"
            <*> v .: "id"
    parseJSON invalid =
        prependFailure "parsing failed, "
            (typeMismatch "Object" invalid)

data NOAAResultset = NOAAResultset
    {
        offset  :: Int
        , count :: Int
        , limit :: Int
    } deriving (Show, Generic)

instance FromJSON NOAAResultset

data NOAAResponseMetadata = NOAAResponseMetadata
    {
        resultset :: NOAAResultset
    } deriving (Show, Generic)

instance FromJSON NOAAResponseMetadata

data NOAAResponse = NOAAResponse
    {
        metadata  :: NOAAResponseMetadata
        , results :: [NOAAResult]
    } deriving (Show, Generic)

instance FromJSON NOAAResponse

printResults :: Maybe [NOAAResult] -> IO ()
printResults Nothing = putStrLn "error loading data"
printResults (Just rs) = do
    forM_ rs $ \r -> do
        print $ mconcat ["|",uid r
          ,"|", mindate r
          ,"|", maxdate r
          ,"|",name r
          ,"|", floatToText $ datacoverage r
          ,"|",resultId r
          ,"|"]

-- Convert 'Float' to 'Text'.
-- Why do we need bothering the String, ByteString, Text etc???
floatToText :: Float -> T.Text
floatToText v= T.pack $ show v

noaaFromJson :: LC.ByteString -> Maybe NOAAResponse
noaaFromJson = decode

