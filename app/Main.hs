{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric #-} 
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where
import Graphics.Gloss
import Function1
import Function2
import Function3
import FieldAndOther
import Data.Sequence as S
import Picosat
import Text.JSON.Generic
import Data.List as L
import Data.Maybe 

exInd :: (Field, S.Seq (S.Seq (S.Seq Int)), S.Seq (S.Seq (S.Seq Int)), Int) -> Int
{-# INLINE exInd #-} 
exInd (_, _, _, i) = i

exField :: (Field, S.Seq (S.Seq (S.Seq Int)), S.Seq (S.Seq (S.Seq Int)), Int) -> Field
{-# INLINE exField #-} 
exField (field, _, _, _) = field

exPos :: (Field, S.Seq (S.Seq (S.Seq Int)), S.Seq (S.Seq (S.Seq Int)), Int) -> S.Seq (S.Seq (S.Seq Int))
{-# INLINE exPos #-} 
exPos (_, sp, _, _) = sp

exBoard :: (Field, S.Seq (S.Seq (S.Seq Int)), S.Seq (S.Seq (S.Seq Int)), Int) -> S.Seq (S.Seq (S.Seq Int))
{-# INLINE exBoard #-} 
exBoard (_, _, b, _) = b

data ParsF = ParsF {
    ver :: [[Int]],
    hor :: [[Int]]
} deriving (Data, Typeable, Show)

drawF :: (Ord a, Num a) => [a] -> Int -> Int -> Picture
{-# INLINE drawF #-} 
drawF arr rows cols= scale (1/fromIntegral(cols * rows)) (1/fromIntegral(cols * rows)) $ pictures [square x | x <- [0..(rows * cols - 1)]]
  where square x =
          Color (if (arr !! x) < 0 && ((0 <= x) && (x <= cols * rows + 1)) then red else black) $
          translate (fromIntegral (x `mod` cols) + 0.5) (-fromIntegral (x `div` cols) - 0.5) $ rectangleSolid 1 1

solA :: Solution -> [Int]
{-# INLINE solA #-} 
solA (Solution b) = b

main :: IO ()
main = do 
    prs <- getLine 
    let prsF = decodeJSON prs :: ParsF
    let mainField = Field  {rowsF = 0, columnsF = 0, horF = toS (hor prsF), verF = toS (ver prsF), clausesF = S.empty}
    let curField = mainField
    let mainField = rebuildFieldVer curField
    let rowsField = rowsF mainField
    let columnsField = columnsF mainField 
    let sizeR = rowsField * columnsField
    let maxk = maxRCField mainField
    let layers = layersField sizeR maxk
    let board = boardField sizeR
    let startPos = startPosField sizeR
    newF <- func1 mainField 1 layers sizeR startPos 0 board 

    let mainField = exField newF
    let startPos = exPos newF
    let ind = exInd newF
    let board = exBoard newF
    newF <- func1 mainField 0 layers sizeR startPos ind board 

    let mainField = exField newF
    let board = exBoard newF
    let startPos = exPos newF
    newF <- func2 mainField board

    let mainField = newF
    newF <- func3 mainField sizeR startPos board

    let mainField = newF
    let sol = toL $ clausesF mainField
    solF <- solve sol
    let sola = solA solF
    men <- display (InWindow "Layout" (1000, 1000) (10,10)) white $ translate (-500) 350 $ scale 15000 15000 $ drawF sola rowsField columnsField
    return men
