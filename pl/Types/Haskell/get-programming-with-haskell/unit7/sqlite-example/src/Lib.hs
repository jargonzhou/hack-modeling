module Lib
    (printTools
    ,addUser
    ,printUsers
    ,checkout
    ,checkinAndUpdate
    ,printAvailable
    ,printCheckedout)
where

import           Control.Applicative    ()
import           Data.Time              (Day, UTCTime (utctDay), getCurrentTime)
import           Database.SQLite.Simple (Connection, FromRow (..), Only (Only),
                                         Query, close, execute, field, open,
                                         query, query_)

data Tool = Tool
    {
        toolId          :: Int
        ,name           :: String
        , description   :: String
        , lastReturned  :: Day
        , timesBorrowed :: Int
    }
instance Show Tool where
    show tool = mconcat [show $ toolId tool
        , ".) "
        , name tool
        , "\n description: "
        , description tool
        , "\n last returned: "
        , show $ lastReturned tool
        , "\n times borrowed: "
        , show $ timesBorrowed tool]
instance FromRow Tool where
    fromRow = Tool <$> field
        <*> field
        <*> field
        <*> field
        <*> field

data User = User
    {
        userId     :: Int
        , userName :: String
    }
instance Show User where
    show user = mconcat [show $ userId user
        , ".) "
        , userName user]
instance FromRow User where
    fromRow = User <$> field
        <*> field

withConn :: String -> (Connection -> IO ()) -> IO ()
withConn dbName action = do
    conn <- open dbName
    action conn
    close conn

-- DEV_ENV: The SQLite database file.
databaseName :: String
databaseName = "D:\\workspace\\application-store\\sqlite\\data\\tools.db"

printToolQuery :: Query -> IO ()
printToolQuery q = withConn databaseName $
    \conn -> do
        resp <- query_ conn q :: IO [Tool]
        mapM_ print resp

printTools :: IO ()
printTools = printToolQuery "SELECT * FROM tools;"

selectTool :: Connection -> Int -> IO (Maybe Tool)
selectTool conn _toolId = do
    resp <- query conn "SELECT * FROM tools WHERE id = (?)"
        (Only _toolId) :: IO [Tool]
    return $ firstOrNothing resp

firstOrNothing :: [a] -> Maybe a
firstOrNothing []    = Nothing
firstOrNothing (x:_) = Just x

addUser :: String -> IO ()
addUser _userName = withConn databaseName $
    \conn -> do
        execute conn "INSERT INTO users (username) VALUES (?)"
            (Only _userName)
        putStrLn "user added"

updateTool :: Tool -> Day -> Tool
updateTool tool date =
    tool {
        lastReturned = date
        , timesBorrowed = 1 + timesBorrowed tool
    }

updateOrWarn :: Maybe Tool -> IO ()
updateOrWarn Nothing = putStrLn "id not found"
updateOrWarn (Just tool) = withConn databaseName $
    \conn -> do
        let q = mconcat ["UPDATE tools SET "
                , "lastReturned = ?, "
                , "timesBorrowed = ? "
                , "WHERE id = ?"]
        execute conn q (lastReturned tool, timesBorrowed tool, toolId tool)
        putStrLn "tool updated"

updateToolTable :: Int -> IO ()
updateToolTable _toolId = withConn databaseName $
    \conn -> do
        tool <- selectTool conn _toolId
        currentDay <- utctDay <$> getCurrentTime
        let updatedTool = updateTool <$> tool <*> pure currentDay
        updateOrWarn updatedTool

printUsers :: IO ()
printUsers = withConn databaseName $
    \conn -> do
        resp <- query_ conn "SELECT * FROM users;" :: IO [User]
        mapM_ print resp

checkout :: Int -> Int -> IO ()
checkout _userId _toolId = withConn databaseName $
    \conn -> do
        execute conn "INSERT INTO checkedout (user_id, tool_id) VALUES (?,?)"
            (_userId, _toolId)

checkin :: Int -> IO ()
checkin _toolId = withConn databaseName $
    \conn -> do
        execute conn "DELETE FROM checkedout WHERE tool_id = (?);" (Only _toolId)

checkinAndUpdate :: Int -> IO ()
checkinAndUpdate _toolId = do
    checkin _toolId
    updateToolTable _toolId

printAvailable :: IO ()
printAvailable = printToolQuery $ mconcat ["SELECT * FROM tools "
    , "WHERE id NOT IN "
    , "(SELECT tool_id FROM checkedout);"]

printCheckedout :: IO ()
printCheckedout = printToolQuery $ mconcat ["SELECT * FROM tools "
    , "WHERE id IN "
    , "(SELECT tool_id FROM checkedout);"]

