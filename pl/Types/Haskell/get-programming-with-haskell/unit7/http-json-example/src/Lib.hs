module Lib
    -- ( requestDatasets
    -- ) 
    where

import qualified Data.ByteString.Char8      as BC

import Network.HTTP.Simple
    ( defaultRequest,
      getResponseBody,
      getResponseStatusCode,
      httpLBS,
      setRequestHeader,
      setRequestHost,
      setRequestMethod,
      setRequestPath,
      setRequestPort,
      setRequestSecure,
      Request )

import NOAA ( printResults, noaaFromJson, results )

noaaToken :: BC.ByteString
noaaToken = "<change_me>" -- request token: https://www.ncdc.noaa.gov/cdo-web/token

noaaHost :: BC.ByteString
noaaHost = "www.ncdc.noaa.gov"

noaaApiPath :: BC.ByteString
noaaApiPath = "/cdo-web/api/v2/datasets"

buildRequest :: BC.ByteString -> BC.ByteString -> BC.ByteString -> BC.ByteString -> Request
buildRequest token host method path = setRequestMethod method
  $ setRequestHost host
  $ setRequestHeader "token" [token]
  $ setRequestPath path
  $ setRequestSecure True
  $ setRequestPort 443
  $ defaultRequest

request :: Request
request = buildRequest noaaToken noaaHost "GET" noaaApiPath

requestDatasets :: IO ()
requestDatasets = do
  response <- httpLBS request -- LBS: Lazy ByteString
  let status = getResponseStatusCode response
  if status == 200
    then do
      let responseBody = getResponseBody response -- ByteString
    --   print responseBody
      let noaaResponse = noaaFromJson responseBody
      printResults $ results <$> noaaResponse
    else putStrLn "request failed with error"
