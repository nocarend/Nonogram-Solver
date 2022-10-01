-- в ~10 раз медленее
{-# LANGUAGE DeriveGeneric #-} -- from docs
-- # {"hor":[[3,1],[1,1,3],[1,2],[2,1,1,2],[1,3],[1,1],[2,1,2],[1,1,3],[1,2],[3,3]],"ver":[[4],[2,2],[1,1],[1,1,1,1],[1,1],[10],[1,1,1,1],[1,1,1,1],[1,1,1,1],[2,1,1,1]]}

-- ind = 0
-- print(len(clauses))
-- for i in clauses:
--     g.add_clause(i)
-- print(g.solve())
-- kek = [['.'] * m for i in range(n)]
-- for i in g.get_model():
--     if 0 < i <= size:
--         kek[(i - 1) // m][(i - 1) % m] = 'O'
-- for i in kek[::-1]:
--     print(*i)
-- в остальное надор жеска вчитываться
module Lib where
import SAT.MiniSat as M
import Data.Aeson
import GHC.Generics
import Control.Monad.State
import Data.IORef
import Control.Concurrent.ParallelIO.Global
import HaskellWorks.Control.Monad.Lazy
import Data.Sequence as S
-- import Data.ByteString.Lazy.Char8 as BC

-- type Count = Int 
-- data Character = Character {c0 :: Int, c1 :: Int, c2 :: Int, c3 :: Int, c4 :: Int, c5 :: Int}
data Field v = Field {
    rows :: Int,
    columns :: Int,
    hor :: S.Seq (S.Seq Int),
    ver :: S.Seq (S.Seq Int),
    clauses :: S.Seq (S.Seq Int)
} deriving (Show, Eq)

-- instance ToJSON Field where
--     -- No need to provide a toJSON implementation.

--     -- For efficiency, we write a simple toEncoding implementation, as
--     -- the default version uses toJSON.
--     toEncoding = genericToEncoding defaultOptions

-- instance FromJSON Field
--     -- No need to provide a parseJSON implementation.

replace :: Int -> a -> S.Seq a -> S.Seq a
replace pos newVal seq = (S.take pos seq |> newVal) >< (S.drop (pos + 1) seq)

tMod :: S.Seq Int -> IO (S.Seq Int -> IO (S.Seq Int))
tMod t = do
    r <- newIORef t
    return (\i -> do 
        if S.null i then do
             modifyIORef' r (\l -> S.empty)
             readIORef r
        else if index i 0 == 0 then do
            modifyIORef' r (\l -> l)
            readIORef r
        else do
            modifyIORef' r (\l -> l >< i) 
            readIORef r)

incrInd :: Int -> IO (Int -> IO Int) -- сам счётчик 
incrInd val = do
    r <- newIORef val
    return (\i -> do 
        modifyIORef' r (+ i)
        readIORef r)
curInd :: Int -> IO (Int -> IO Int) -- сам счётчик 
curInd val = do
    r <- newIORef val
    return (\i -> do 
        if i == 0 then do
            modifyIORef' r (\l -> l) 
            readIORef r
        else do
            modifyIORef' r (\l -> i) 
            readIORef r)
ffInd :: Int -> IO (Int -> IO Int) -- сам счётчик 
ffInd val = do
    r <- newIORef val
    return (\i -> do 
        if i == 0 then do
            modifyIORef' r (\l -> l) 
            readIORef r
        else do
            modifyIORef' r (\l -> i) 
            readIORef r)
clausesAdding :: Field Int -> IO (S.Seq Int -> IO (Field Int)) -- Добавляем клозы
clausesAdding field = do
    r <- newIORef field 
    return (\i -> do
        if S.null i then do
            modifyIORef' r (\l -> l) 
            readIORef r
        else do
            modifyIORef' r (\l -> l {clauses = (clauses l) |> i}) 
            readIORef r)

sPing :: S.Seq (S.Seq (S.Seq Int)) -> IO (Int -> S.Seq Int -> IO (S.Seq (S.Seq (S.Seq Int)))) -- Добавляем ... done 
sPing pos = do
    r <- newIORef pos 
    return (\i j -> do 
        if S.null j then do
             modifyIORef' r (\l -> l)
             readIORef r
        else do
            modifyIORef' r (\l -> replace i ((l `index` i) |> j) l) 
            readIORef r)

boarding :: S.Seq (S.Seq (S.Seq Int)) -> IO (Int -> S.Seq Int -> IO (S.Seq (S.Seq (S.Seq Int))))
boarding board = do
    r <- newIORef board
    return (\i j -> do
        if S.null j then do
             modifyIORef' r (\l -> l)
             readIORef r
        else do
            modifyIORef' r (\l -> replace i ((l `index` i) |> j) l) 
            readIORef r)

goodMod :: Int -> Int -> Int
goodMod a b
 | a `mod` b == 0 = b
 | otherwise = a `mod` b

toL :: [[Int]] -> S.Seq (S.Seq Int)
toL l = S.fromList $ map (S.fromList) l 

rebuildFieldVer :: Field Int -> Field Int -- добавляем нолики, вычисляем m & n
rebuildFieldVer field = field {ver = (toL [[]]) >< (S.mapWithIndex (\i j -> (0 <| j)) (ver field)), hor = (toL [[]]) >< (S.mapWithIndex (\i x -> 0 <| (S.reverse x)) (hor field)),
 rows = S.length (ver field), columns = S.length (hor field)}

sizeField :: Field Int -> Int -- вычисляем size
sizeField field = (rows field) * (columns field)

maxRCField :: Field Int -> Int -- поиск максимальной длины подмассива
maxRCField field = max (S.foldlWithIndex (\a c b -> max a (S.length b)) 0 (ver field)) (foldlWithIndex (\a c b -> max a (S.length b)) 0 (hor field))

layersField :: Int -> Int -> S.Seq Int -- слои
layersField sizeF maxF= S.fromList $ [sizeF * i | i <- [0..2 * maxF + 1]]

boardField :: Int -> S.Seq (S.Seq (S.Seq Int)) -- поле не помню
boardField sizeF = S.replicate (sizeF + 1) S.empty

startPosField :: Int -> S.Seq (S.Seq (S.Seq Int)) -- стартовая позиция не помню
startPosField sizeF = S.replicate (sizeF + 1) S.empty

func1 :: Field Int -> Int -> S.Seq Int -> Int -> S.Seq (S.Seq (S.Seq Int)) -> Int -> S.Seq (S.Seq (S.Seq Int)) -> 
    IO (Field Int, S.Seq (S.Seq (S.Seq Int)), S.Seq (S.Seq (S.Seq Int)), Int) -- сделал 
func1 mfield nol layers sizeF sP stInd sBoard = do
    clAd <- clausesAdding mfield
    spAdd <- sPing sP
    plInd <- incrInd stInd
    bAdd <- boarding sBoard
    tAdd <- tMod S.empty
    field <- clAd S.empty
    startPos <- spAdd 0 S.empty
    ind <- plInd 0
    board <- bAdd 0 S.empty
    let st1 = mfunc where
        mfunc :: IO ()
        mfunc = do
            let p = sequence (map funcI [1..rangeI]) where
                rangeI :: Int
                rangeI 
                    | nol == 1 = rows mfield 
                    | otherwise = columns mfield
                funcI :: Int -> IO [()]
                funcI indexI = sequence (map funcJ [1..(S.length ((rangeJ (hor mfield) (ver mfield)) `index` indexI) - 1)]) where
                    rangeJ :: S.Seq (S.Seq Int) -> S.Seq (S.Seq Int) -> S.Seq (S.Seq Int)
                    rangeJ lenH lenV
                        | nol == 1 = lenV
                        | otherwise = lenH
                    funcJ :: Int -> IO ()
                    funcJ indexJ = do
                        let cur = 2 * indexJ - nol
                        t <- tAdd S.empty
                        let funcK = sequence (map inK rangeK) where 
                            rangeK :: [Int]
                            rangeK 
                                | nol == 1 = [(layers `index` cur + (indexI - 1) * (columns mfield) + 1)..(layers `index` cur + 
                                indexI * (columns mfield) + 1 - (ver mfield) `index` indexI `index` indexJ)]
                                | otherwise = [(layers `index` (cur + 1)) - columns mfield + indexI, ((layers `index` (cur + 1)) - 
                                2 * (columns mfield) + indexI)..(layers `index` cur + indexI + ((((hor mfield) `index` indexI) `index` 
                                indexJ) - 1) * (columns mfield))]
                            inK :: Int -> IO ()
                            inK indexK = do
                                t <- tAdd (S.fromList [indexK])
                                let l1 = goodMod indexK sizeF
                                ind <- plInd 0
                                let pep = spAdd l1 (S.fromList [indexK, nol, (mas `index` indexI) `index` indexJ, ind, indexI, indexJ]) where-- 
                                    mas :: S.Seq (S.Seq Int)
                                    mas 
                                        | nol == 1 = ver mfield
                                        | otherwise = hor mfield
                                startPos <- pep
                                let st2 = sequence (map funcP rangeP) where
                                    rangeP :: [Int]
                                    rangeP 
                                        | nol == 1 = [indexK..(indexK + (ver mfield `index` indexI) `index` indexJ - 1)]
                                        | otherwise = [indexK, (indexK - columns mfield)..(indexK - (((hor mfield) `index` indexI) `index` 
                                        indexJ) * (columns mfield) + 1)]
                                    funcP :: Int -> IO ()
                                    funcP indexP = do
                                        let l1 = goodMod indexP sizeF
                                        board <- bAdd l1 (S.fromList [indexK, ind, nol, indexI, indexJ]) 
                                        return ()
                                sst <- st2
                                return ()
                        kFunc <- funcK
                        ind <- plInd 1
                        t <- tAdd (S.fromList [0])
                        let s1 = sequence (map funcS1 [0..(S.length t - 1)]) where 
                            funcS1 :: Int -> IO ()
                            funcS1 indexS1 = do
                                let s2 = sequence (map funcS2 [(indexS1 + 1)..(S.length t - 1)]) where
                                    funcS2 :: Int -> IO ()
                                    funcS2 indexS2 = do
                                        let tt = [-(t `index` indexS1), -(t `index` indexS2)]
                                        field <- clAd (S.fromList tt)
                                        return ()
                                ss2 <- s2
                                return ()
                        ss1 <- s1
                        field <- clAd t
                        return ()
            ppp <- p
            return ()
    kkkk <- st1
    ind <- plInd 0
    startPos <- spAdd 0 S.empty
    board <- bAdd 0 S.empty
    field <- clAd S.empty
    return (field, startPos, board, ind)

func2 :: Field Int -> S.Seq (S.Seq (S.Seq Int)) -> IO (Field Int) -- сделал
func2 mfield sBoard = do
    clAd <- clausesAdding mfield
    tAdd <- tMod S.empty
    field <- clAd S.empty
    let fI = sequence (map funcI [1..(S.length sBoard - 1)]) where
        funcI :: Int -> IO ()
        funcI indexI = do
            pt <- tAdd S.empty
            pt <- tAdd (S.fromList [-indexI])
            let fJ = sequence (map funcJ [0..(S.length (sBoard `index` indexI) - 1)]) where
                funcJ :: Int -> IO ()
                funcJ indexJ = do
                    pt <- tAdd (S.fromList [sBoard `index` indexI `index` indexJ `index` 0])
                    let t = [indexI, -sBoard `index` indexI `index` indexJ `index` 0]
                    field <- clAd (S.fromList t)
                    return ()
            ffJ <- fJ
            pt <- tAdd (S.fromList [0])
            field <- clAd pt
            return ()
    ffI <- fI
    field <- clAd S.empty
    return field

func3 :: Field Int -> Int -> S.Seq (S.Seq (S.Seq Int)) ->  S.Seq (S.Seq (S.Seq Int)) -> IO (Field Int) -- net
func3 mfield sizeF startPos sBoard = do
    clAd <- clausesAdding mfield
    tAdd <- tMod S.empty
    field <- clAd S.empty
    curCh <- curInd 0
    ffCh <- ffInd 0
    let board = sBoard
    let fI = sequence (map funcI [1..sizeF]) where
        funcI :: Int -> IO [()]
        funcI indexI = sequence (map funcJ [0..(S.length (startPos `index` indexI) - 1)]) where
            funcJ :: Int -> IO ()
            funcJ indexJ = do
                let newPos = startPos `index` indexI `index` indexJ `index` 2
                let fK = sequence (map funcK rangeK) where
                    rangeK :: [Int]
                    rangeK
                        | startPos `index` indexI `index` indexJ `index` 1 == 0 = [(indexI - (columns mfield) * (newPos - 1)),
                        (indexI - (columns mfield) * (newPos - 2))..indexI]
                        | otherwise = [indexI..(indexI + newPos - 1)]
                    funcK :: Int -> IO ()
                    funcK indexK = do
                        t <- tAdd S.empty
                        t <- tAdd (S.fromList [-startPos `index` indexI `index` indexJ `index` 0]) 
                        cur <- curCh 0     
                        ff <- ffCh 0
                        t <- tAdd (S.fromList [0])
                        let fP = sequence (map funcP [0..(S.length (board `index` indexK) - 1)]) where
                            funcP :: Int -> IO ()
                            funcP indexP = do
                                t <- tAdd (S.fromList [0])
                                ff <- ffCh 0
                                cur <- curCh 0
                                t <- tAdd (S.fromList [0])
                                if (indexP == (S.length (board `index` indexK) - 1)) && (S.length t) > 1 then do
                                    t <- tAdd (S.fromList [0])
                                    field <- clAd t
                                    return ()
                                else do
                                    return ()
                                ff <- ffCh 0
                                cur <- curCh 0
                                if (board `index` indexK `index` indexP `index` 1 /= startPos `index` indexI `index` indexJ `index` 3) && (board `index` indexK `index` indexP `index` 2 /= startPos `index` indexI `index` indexJ `index` 1) then do
                                    if (t == (S.fromList [-startPos `index` indexI `index` indexJ `index` 0])) || (cur == board `index` indexK `index` indexP `index` 1) || ((cur /= board `index` indexK `index` indexP `index` 1) && (ff == board `index` indexK `index` indexP `index` 3)) then do
                                            t <- tAdd (S.fromList [0])
                                            t <- tAdd (S.fromList [board `index` indexK `index` indexP `index` 0])
                                            return ()
                                    else do
                                        t <- tAdd (S.fromList [0])
                                        field <- clAd t
                                        t <- tAdd S.empty
                                        t <- tAdd (S.fromList [-startPos `index` indexI `index` indexJ `index` 0, board `index` indexK `index` indexP `index` 0])
                                        return ()
                                    t <- tAdd (S.fromList [0])
                                    cur <- curCh (board `index` indexK `index` indexP `index` 1)     
                                    ff <- ffCh (board `index` indexK `index` indexP `index` 3)  
                                    t <- tAdd (S.fromList [0])
                                    if indexP == (S.length (board `index` indexK) - 1) || ((board `index` indexK `index` (indexP + 1) `index` 1 
                                        /= cur) && (ff /= board `index` indexK `index` (indexP + 1) `index` 3)) then do
                                            t <- tAdd (S.fromList [0])
                                            field <- clAd t
                                            t <- tAdd S.empty
                                            t <- tAdd (S.fromList [-startPos `index` indexI `index` indexJ `index` 0])
                                            return ()
                                    else do
                                        t <- tAdd (S.fromList [0])
                                        return ()
                                    ff <- ffCh ff
                                    cur <- curCh cur
                                    t <- tAdd (S.fromList [0])
                                    return ()
                                else do
                                    ff <- ffCh ff
                                    cur <- curCh cur
                                    t <- tAdd (S.fromList [0])
                                    return ()
                                -- mm <- mem
                                ff <- ffCh 0
                                cur <- curCh 0
                                t <- tAdd (S.fromList [0])
                                return ()
                        ffP <- fP
                        return ()
                ffK <- fK
                let fK = sequence (map funcK rangeK) where
                    rangeK :: [Int]
                    rangeK
                        | startPos `index` indexI `index` indexJ `index` 1 == 0 = [indexI, (indexI - columns field)..1]
                        | otherwise = [indexI..(((indexI - 1) `div` (columns field) + 1) * (columns field))]
                    funcK :: Int -> IO [()]
                    funcK indexK = sequence (map funcT [0..(S.length (startPos `index` indexK) - 1)]) where
                        funcT :: Int -> IO ()
                        funcT indexT = do
                            if (startPos `index` indexK `index` indexT `index` 3 /= startPos `index` indexI `index` indexJ `index` 3) 
                                && (startPos `index` indexI `index` indexJ `index` 1 == startPos `index` indexK `index` indexT `index` 1) 
                                && (startPos `index` indexI `index` indexJ `index` 5 > startPos `index` indexK `index` indexT `index` 5) 
                                then do
                                    field <- clAd (S.fromList [-startPos `index` indexI `index` indexJ `index` 0, -startPos `index` indexK `index` indexT `index` 0])
                                    return ()
                            else do
                                return ()
                            return ()
                ffK <- fK  
                if startPos `index` indexI `index` indexJ `index` 1 == 0 then do
                    if indexI - (columns field) * newPos > 0 then do
                        let fK = sequence (map funcK [0..(S.length (board `index` (indexI - (columns field) * newPos)) - 1)]) where
                            funcK :: Int -> IO ()
                            funcK indexK = do
                                if (startPos `index` indexI `index` indexJ `index` 0 - 1) `div` sizeF /= (board `index` 
                                     (indexI - (columns field) * newPos) `index` indexK `index` 0 - 1) `div` sizeF then do
                                        field <- clAd (S.fromList [-startPos `index` indexI `index` indexJ `index` 0, -board `index` (indexI - (columns field) * newPos) `index` indexK `index` 0])
                                        return ()
                                else do
                                    return ()
                                return ()
                        ffK <- fK
                        return ()
                    else do
                        return ()
                    if indexI + (columns field) <= sizeF then do
                        let fK = sequence (map funcK [0..(S.length (board `index` (indexI + columns field)) - 1)]) where
                            funcK :: Int -> IO ()
                            funcK indexK = do
                                if (startPos `index` indexI `index` indexJ `index` 0 - 1) `div` sizeF /= (board `index` (indexI + columns field) `index` indexK `index` 0 - 1) `div` sizeF then do
                                    field <- clAd (S.fromList [-startPos `index` indexI `index` indexJ `index` 0, -board `index` (indexI + columns field) `index` indexK `index` 0])
                                    return ()
                                else do
                                    return ()
                        ffK <- fK
                        return ()
                    else do
                        return ()
                    return ()
                else do
                    if (indexI - 1) `div` (columns field) == (indexI + newPos - 1) `div` (columns field) then do
                        let fK = sequence (map funcK [0..(S.length (board `index` (indexI + newPos)) - 1)]) where
                            funcK :: Int -> IO ()
                            funcK indexK = do
                                if (startPos `index` indexI `index` indexJ `index` 0 - 1) `div` sizeF /= (board `index` 
                                     (indexI + newPos) `index` indexK `index` 0 - 1) `div` sizeF then do
                                        field <- clAd (S.fromList [-startPos `index` indexI `index` indexJ `index` 0, -board `index` (indexI + newPos) `index` indexK `index` 0])
                                        return ()
                                else do
                                    return ()
                                return ()
                        ffK <- fK
                        return ()
                    else do
                        return ()
                    if (indexI - 1) `div` (columns field) == (indexI - 2) `div` (columns field) then do
                        let fK = sequence (map funcK [0..(S.length (board `index` (indexI - 1)) - 1)]) where
                            funcK :: Int -> IO ()
                            funcK indexK = do
                                if (startPos `index` indexI `index` indexJ `index` 0 - 1) `div` sizeF /= (board `index`
                                     (indexI - 1) `index` indexK `index` 0 - 1) `div` sizeF then do
                                        field <- clAd (S.fromList [-startPos `index` indexI `index` indexJ `index` 0, -board `index` (indexI - 1) `index` indexK `index` 0])
                                        return ()
                                else do
                                    return ()
                        ffK <- fK
                        return ()
                    else do
                        return ()
                    return ()
                return ()
    ffI <- fI
    field <- clAd S.empty
    return (field)
-- --rawJson :: BC.ByteString -> BC.ByteString -- парсер
-- -- rawJson a = "{\"hor\":[[],[],[2,3]],\"ver\":[[1,2],[]]}" -- = a

-- -- fieldFromJson :: Maybe Field
-- -- fieldFromJson = decode rawJson


-- kek = (Var 1) :&&: (Not $ Var 2)
-- -- tet = Not $ Var 2 

-- tet = solve_all kek