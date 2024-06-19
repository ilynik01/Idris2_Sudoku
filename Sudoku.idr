module Sudoku

import Data.Fin
import Data.Vect
import Data.Nat
import Data.String 
import System.File  


-- A fully documented Idris code
-- examples to test the function are shown with `>`:
-- > example_function ex_input




-- This type can handle a sudoku table of any size.
data SudokuTable : (row : Nat) -> (col : Nat) -> (size : Nat) -> Type where
    SVal : Vect size (Vect size (Fin (S size))) -> SudokuTable size size size
    SEdit : Vect row (Vect col (Fin (S size))) -> SudokuTable row col size
    SErr : SudokuTable row col size

s : SudokuTable 9 9 9
s = SVal [[1,2,3,0,0,0,9,8,9],[9,3,3,3,9,3,3,3,9],[1,2,3,4,5,6,7,8,9],[1,2,3,4,5,6,7,8,9],[1,2,3,4,5,6,7,8,9],[1,2,3,4,0,6,7,8,9],[1,2,3,4,5,6,7,8,9],[1,2,3,4,5,6,7,8,9],[1,2,3,4,5,6,7,8,9]]






-- Evaluates to the number in the SudokuTable type at position (r, c)
-- It does pattern matching and recursive calls and cuts the table as long as
-- it reaches the position of 1 1 in which it tales the x value.
index : SudokuTable row col size -> Nat -> Nat -> Maybe Nat
index SErr r c = Nothing
index (SVal xs) r c = index (SEdit xs) r c
index (SEdit []) _ _ = Nothing
index (SEdit ([] :: xs)) _ _ = Nothing
index (SEdit ((x :: ys) :: xs)) _ 0 = Nothing
index (SEdit ((x :: ys) :: xs)) 0 _ = Nothing
index (SEdit ((x :: ys) :: xs)) 1 1 = Just (finToNat x)
index (SEdit ((x :: ys) :: xs)) 1 (S (S c)) = index (SEdit [ys]) 1 (S c)
index (SEdit ((x :: ys) :: xs)) (S (S r)) c = index (SEdit xs) (S r) c
-- > index s 2 2







-- Takes one specific row of table and replaces the value at position (r, c) with the given value
replace : Vect len a -> (col : Nat) -> (v : a) -> Vect len a
replace (a :: as) 0 v = (a :: as)
replace (a :: as) 1 v = (v :: as)
replace (a :: as) (S (S c)) v = (a :: replace as (S c) v)
replace [] _ _ = []

-- The function updates the cell at position (r, c) with the given value
-- It first iterates as much to find the right row, concatenating all the parts in the beginning
-- Then when it finds the right row, it calls `replace` tp iterate to find the right column and replaces the value
-- Of course joining the leftover parts with the rest.
update : SudokuTable row col n -> Nat -> Nat -> Fin (S n) -> SudokuTable row col n
update SErr r c v = SErr
update (SVal xs) r c v = update (SEdit xs) r c v
update (SEdit []) _ _ _ = SErr
update (SEdit ([] :: xs)) _ _ _ = SErr
update (SEdit ((x :: ys) :: xs)) 0 _ v = SErr
update (SEdit ((x :: ys) :: xs)) _ 0 v = SErr
update (SEdit ((x :: ys) :: xs)) 1 c v = (SEdit ((replace (x :: ys) c v) :: xs))
update (SEdit ((x :: ys) :: xs)) (S (S r)) c v  with  (update (SEdit xs) (S r) c v)
            _ | (SEdit zs) = SEdit ([x :: ys] ++ zs)
            _ | _ = SErr
-- > tTNM (update sa 1 1 0)

sa : SudokuTable 4 4 4
sa = SEdit [[1,2,3,4],[1,2,3,4],[1,2,3,4],[1,2,3,4]]
-- > tTNM sa


-- May be useful:
-- Turn Fin into Nat in SudokuTable
tTNMt : Vect rows (Vect cols (Fin n)) -> Vect rows (Vect cols Nat)
tTNMt = map (map finToNat)

tTNM : SudokuTable r c n -> Vect r (Vect c Nat)
tTNM (SVal xs) = tTNMt xs
tTNM (SEdit xs) = tTNMt xs
tTNM SErr = ?i_dont_want_to_use_maybe








-- return true if the value is zero
isItZero : Fin a -> Bool
isItZero FZ = True
isItZero (FS e) = False

-- returns the difficulty of a Sudoku grid
-- Does this by counting the number of zeros in the grid and dividing it by the total number of cells
-- The total number of cells is the product of the lengths of rows and columns
difficulty : SudokuTable r c n -> Double
difficulty SErr = 0
difficulty (SVal xs) = difficulty (SEdit xs)
difficulty (SEdit []) = 0
difficulty (SEdit ([] :: xs)) = 0
difficulty (SEdit (x :: xs)) with (map (filter isItZero) (x :: xs))
            _ | (ys) = ((county ys) / ((cast (length (x :: xs))) * (cast (length (x))))) * 100
            where
                county : Vect len (p : Nat ** Vect p (Fin (S n))) -> Double
                county [] = 0
                county (((fst ** snd)) :: xs) = (cast fst) + county xs
-- > difficulty su       

su : SudokuTable 2 4 4
su = SEdit [[1,1,1,3],[2,0,0,0]]
-- > tTNM su







-- This is validation which requires many steps.
-- First of all there is a detailed `Plan` of actions - the description of how validation works.
-- Next goes the `Implemented part`.


-- ________Plan________:
-- -- 1 Step. Take one cell in Table. Get its coordinates `nr`, `nc` and is value `num`
-- --       index su nr nc = Just num    -- Get the value of the cell  
-- --       nr  - coordinate for row (vertical)
-- --       nc  - coordinate for column (horizontal)
-- --   Given a SudokuTable su:
-- --       su = SEdit ((x :: ys) :: xs)
-- --       length of col (all rows): (cast (length ((x :: ys) :: xs)))  = lc
-- --       length of row (all cols): (cast (length (x :: ys)))          = lr
-- --   Therefore:         
--          lc = (cast (length ((x :: ys) :: xs)))
--          lr = (cast (length (x :: ys)))
-- --   NOTE the switch! length of row defines number of col (coordinates)


-- -- 2 Step. Check if `num` appears at most once in row `nr`
-- --   isRowValid: index su nr (length c) == num?    
-- --       iterate:
-- (index su nr (S lr) == num) && ((S lr) /= nc)
--     False => True   -- row is valid
--     True => False   -- row is not valid


-- -- 3. Check if `num` appears at most once in column `nc`
--  isColValid: index su (length r) nc == num?    
-- (index su (S lc) nc == num) && ((S lc) /= nr)
--     False => True   -- col is valid
--     True => False   -- col is not valid


-- -- 4.1 Check the sub grid
-- if lc == lr
--     True => True     -- sudoku table length and width is square and valid
--     False => False   -- sudoku table length and width is NOT square and NOT valid

-- -- is square root whole or fraction?
-- sqCheck : (n : Nat) -> Either () Nat
-- sqCheck n = if (pow (sqrt (cast n)) 2) == (cast n) then Right n else Left ()

-- gridv -- the size of grid. Classical sudoku size is 3.
-- gridv = sqrt (cast lr)
--     True => True     -- Valid. length and width is in accordance to size of grid: 1,2,3,4,...
--     False => False   -- NOT Valid. length and width is NOT in accordance to size of grid: 1,2,3,4,...


-- -- 4.2 isSubGridValid: index su (length r) (length c) == num?   -- Check if `num` appears at most once in 3x3 sub-grid
--   1) create starting points for row and col: stpr, stpc
--   2) walk through each row of subgrid
--   3) walk through each col of subgrid






-- _______Implemented part_______:

-- Step 2
-- Takes coordinates of one cell and mathces its value to values of all other numbers in the row of this cell
isRowValid : SudokuTable r c n -> (lr : Nat) -> (nr : Nat) -> (nc : Nat) -> (num : Nat) ->  Bool
isRowValid su 0 nr nc num = True
isRowValid su (S lr) nr nc num = case ((fromMaybe 0 (index su nr (S lr))) == num) && ((S lr) /= nc) && (num /= 0) of
                False => isRowValid su lr nr nc num
                True => False

-- Step 3
-- Takes coordinates of one cell and mathces its value to values of all other numbers in the column of this cell
isColValid : SudokuTable r c n -> (lc : Nat) -> (nr : Nat) -> (nc : Nat) -> (num : Nat) ->  Bool
isColValid su 0 nr nc num = True
isColValid su (S lc) nr nc num = case ((fromMaybe 0 (index su (S lc) nc)) == num) && ((S lc) /= nr) && (num /= 0) of
                                        False => isColValid su lc nr nc num
                                        True => False


-- Step 4
-- 4.1.1-2) 
-- sqValid: Is grid size valid? Does square root of `lc` leave fraction?
sqValid : (n : Nat) -> Bool
sqValid n = (pow (floor (sqrt (cast n))) 2) == (cast n) 
-- > sqCheck 8; > sqCheck 9

-- gridCheck: Check if we can work with this grid: 1) equal sides; 2) sqrt of a side is not a fraction
gridCheck : (lc : Nat) -> (lr : Nat) -> Bool
gridCheck lc lr = (lc == lr) && (sqValid lc)
-- True    -- Valid. length and width are equal and in accordance to size of grid: 1,2,3,4,...
-- False   -- NOT Valid. length and width are NOT equal or NOT in accordance to size of grid: 1,2,3,4,...

-- 4.1.3) `gridv` -  the size of grid. Classical sudoku size is 3 if lc = 9 of course
gridv : (lc : Nat) -> Nat
gridv lc = cast (sqrt (cast lc))


-- 4.2) Seek the starting point for each nr nc and their num 
-- give it nr/nc coordinate and get the starting point
seekStp : (nrc : Nat) -> (gridv : Nat) -> Nat
seekStp x 0 = 0
seekStp x y = case ((floor (cast x / cast y)) == (cast x / cast y)) of
                    False => cast (floor (cast x / cast y)) * y
                    True => cast ((floor (cast x / cast y)) - 1) * y


-- Checks if `num` value appears in the sub-grid. Function matches `num` to all other numbers and returns Bool.
gridCol : SudokuTable r c n -> (nr : Nat) -> (fnr : Nat) -> (nc : Nat) -> (gridv : Nat) -> (stpc : Nat) -> (num : Nat) -> Bool
gridCol su nr fnr nc 0 stpc num = True
gridCol su nr fnr nc (S gridv) stpc num = case ((fromMaybe 0 (index su fnr (stpc + (S gridv)))) == num) && ((fnr) /= (nr)) && (num /= 0) of  
                        True => False
                        False => gridCol su nr fnr nc gridv stpc num

-- Combine aforementioned functions to check if `num` appears in rows and columns of sub-grid.
gridRow : SudokuTable r c n -> (nr : Nat) -> (nc : Nat) -> (gridv : Nat) -> (stpr : Nat) -> (stpc : Nat) -> (num : Nat) -> Bool
gridRow su nr nc 0 stpr stpc num = True
gridRow su nr nc (S gridv) stpr stpc num = case (gridCol su nr (stpr + (S gridv)) nc (S gridv) stpc num) of
                        True => gridRow su nr nc gridv stpr stpc num
                        False => False

-- Check if `num` appears at most once in sub-grid.s
isGridValid : SudokuTable r c n -> (lc : Nat) -> (lr : Nat) -> (nr : Nat) -> (nc : Nat) -> Bool
isGridValid su lc lr nr nc = case gridCheck lc lr of
                False => False
                True => gridRow su nr nc (gridv lc) (seekStp nr (gridv lc)) (seekStp nc (gridv lc)) (fromMaybe 0 (index su nr nc))
                



-- Step 1. Split the table into different useful data. Iterate over every cell and check if it is valid.
-- Here:
-- nr, nc - coordinates. number of row, number of column. `index nr nc = num`
-- lc, lr - length of row and column, used for short input. not for iteration! 
-- ilc, ilr - iteration variables of row and col
-- input example: colEl su 0 0 (length of col) (length of row) 1 1
colEl : SudokuTable r c n -> (lc : Nat) -> (lr : Nat) -> (ilc : Nat) -> (ilr : Nat) -> (nr : Nat) -> (nc : Nat) -> Bool
colEl su 0 0 ilc ilr nr nc = colEl su ilc ilr ilc ilr nr nc
colEl su lc lr 0 _ nr nc = False
colEl su lc lr _ 0 nr nc = False
colEl su lc lr 1 1 nr nc =   
            case (isRowValid su lr nr nc (fromMaybe 0 (index su nr nc))) &&
                 (isColValid su lc nr nc (fromMaybe 0 (index su nr nc))) &&
                 (isGridValid su lc lr nr nc) of 
                        True => True
                        False => False
colEl su lc lr (S ilc) 1 nr nc =   
            case (isRowValid su lr nr nc (fromMaybe 0 (index su nr nc))) &&
                 (isColValid su lc nr nc (fromMaybe 0 (index su nr nc))) &&
                 (isGridValid su lc lr nr nc) of 
                        True => colEl su lc lr ilc nc (nr + 1) 1
                        False => False
colEl su lc lr (S ilc) (S ilr) nr nc =   
            case (isRowValid su lr nr nc (fromMaybe 0 (index su nr nc))) &&
                 (isColValid su lc nr nc (fromMaybe 0 (index su nr nc))) &&
                 (isGridValid su lc lr nr nc) of 
                        True => colEl su lc lr (S ilc) (ilr) nr (nc + 1)
                        False => False

 -- I know that I can make it shorter and I tried it in my draft but I have intentionally left it that big for debugging.
 -- It is easy to put a hole somewhere in here and see to what extent the program did work.
 



-- Finally the function isValid itself. It checks if the SudokuTable type is valid.
isValid : SudokuTable r c n -> Bool
isValid SErr = False
isValid (SVal xs) = isValid (SEdit xs)
isValid (SEdit []) = False 
isValid (SEdit ([] :: xs)) = False
isValid (SEdit ((x :: ys) :: xs)) = (colEl (SEdit ((x :: ys) :: xs)) 0 0 (length ((x :: ys) :: xs)) (length (x :: ys)) 1 1)



-- Tests for isValid function
test : SudokuTable 4 4 4
test = SVal [[1,2,3,4],[3,4,1,2],[2,3,4,1],[4,1,2,3]]

ztest : SudokuTable 4 4 4
ztest = SVal [[0,0,3,4],[0,4,1,2],[2,3,4,1],[4,1,2,3]]

invtest : SudokuTable 4 5 4
invtest = SEdit [[1,2,3,4,4],[3,4,1,2,0],[2,3,4,1,0],[4,1,2,3,0]]

inv_tabletest : SudokuTable 9 9 9    -- NOT VALID
inv_tabletest = SVal [[5,3,3,0,7,0,0,0,0],
                      [6,0,0,1,9,5,0,0,0],
                      [0,9,8,0,0,0,0,6,0],
                      [8,0,0,0,6,0,2,0,3],
                      [4,0,0,8,0,3,2,0,1],
                      [7,0,0,0,2,0,2,0,6],
                      [0,6,0,0,0,0,2,8,0],
                      [0,0,0,4,1,9,0,0,5],
                      [0,0,0,0,8,0,0,7,9]]

valid_tabletest : SudokuTable 9 9 9    -- VALID
valid_tabletest = SVal [[5,3,0,0,7,0,0,0,0],
                        [6,0,0,1,9,5,0,0,0],
                        [0,9,8,0,0,0,0,6,0],
                        [8,0,0,0,6,0,0,0,3],
                        [4,0,0,8,0,3,0,0,1],
                        [7,0,0,0,2,0,0,0,6],
                        [0,6,0,0,0,0,2,8,0],
                        [0,0,0,4,1,9,0,0,5],
                        [0,0,0,0,8,0,0,7,9]]







-- Checks if the SudokuTable is complete. It is complete if it is valid and has all cells filled (difficulty == 0).
isComplete : SudokuTable r c n -> Bool
isComplete su = isValid su && (difficulty su == 0)

-- Tests for isComplete function
cpl : SudokuTable 4 4 4
cpl = SVal [[1,2,3,4],[3,4,1,2],[2,3,4,1],[4,1,2,3]]

ncpl : SudokuTable 4 4 4
ncpl = SVal [[0,0,3,4],[0,4,1,2],[2,3,4,1],[4,1,2,3]]









-- Parser that can read a Sudoku table from a file

-- String to Nat
strToNat1 : String -> Nat
strToNat1 val = cast (fromString val)
-- > strToNat "0"

-- Nat to Fin n
nat2Fin1 : (n : Nat) -> Fin (S n)
nat2Fin1 Z = FZ
nat2Fin1 (S i) = FS (nat2Fin1 i)
-- > natToFin 3



strToSudoku : String -> SudokuTable 9 9 9
strToSudoku str = SVal (makeRow 0 (lines str))
     where
        makeRow : (c : Nat) -> List String -> Vect 9 (Vect 9 (Fin (S 9)))
        makeRow c strng = ?fdgdgfdfg



-- Output of readFile:
-- "[[5,3,0,0,7,0,0,0,0],\n[6,0,0,1,9,5,0,0,0],\n[0,9,8,0,0,0,0,6,0],\n[8,0,0,0,6,0,0,0,3],\n[4,0,0,8,0,3,0,0,1],\n[7,0,0,0,2,0,0,0,6],\n[0,6,0,0,0,0,2,8,0],\n[0,0,0,4,1,9,0,0,5],\n[0,0,0,0,8,0,0,7,9]]"

-- "sudo.txt"
parse : IO (SudokuTable 9 9 9)
parse = readFile "sudo.txt" >>= 
            \text => case text of
                Left ext => ?aaaaaaa
                Right te => pure (strToSudoku te)

-- te = "[[5,3,0],\n[6,0,0],\n[0,9,8]]"
-- lines te

-- ["[[5,3,0],", "[6,0,0],", "[0,9,8]]"]


-- "[[5,3,0],"
cleanStr : String -> String
cleanStr str = pack (unPacked (unpack str))
    where
        unPacked : List Char -> List Char
        unPacked cs = Prelude.List.filter (\c => isDigit c || c == ',') cs

-- "5,3,0,"









