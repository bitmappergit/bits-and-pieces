import System.Environment ( getArgs )
import Data.Unique ( hashUnique, newUnique )

data Op
  = Inc Int
  | Dec Int
  | Shl Int
  | Shr Int
  | Prn
  | Inp
  | Jmp [Op]

data AsmOp
  = Add Int
  | Sub Int
  | ShiftL Int
  | ShiftR Int
  | Print
  | Input
  | Label Int 
  | EndLabel Int
  | Clear

parse :: ([Char], [Op]) -> ([Char], [Op])
parse ('+' : cs, acc) = parse (cs, Inc 1 : acc)
parse ('-' : cs, acc) = parse (cs, Dec 1 : acc)
parse ('>' : cs, acc) = parse (cs, Shr 1 : acc)
parse ('<' : cs, acc) = parse (cs, Shl 1 : acc)
parse ('.' : cs, acc) = parse (cs, Prn : acc)
parse (',' : cs, acc) = parse (cs, Inp : acc)
parse ('[' : cs, acc) = parse (newCs, Jmp loop : acc)
  where (newCs, loop) = parse (cs, [])
parse (']' : cs, acc) = (cs, reverse acc)
parse ([], acc) = ([], reverse acc)
parse (_ : cs, acc) = parse (cs, acc)

opt :: [Op] -> IO [AsmOp]
opt (Jmp [Dec 1] : xs) = (Clear :) <$> opt xs
opt (Jmp [Inc 1] : xs) = (Clear :) <$> opt xs
opt (Jmp x : xs) = do
  hash <- fmap hashUnique newUnique
  body <- opt x
  rest <- opt xs
  pure $ Label hash : body ++ EndLabel hash : rest 
opt (Inc x : xs) = (Add x :) <$> opt xs
opt (Dec x : xs) = (Sub x :) <$> opt xs
opt (Shr x : xs) = (ShiftR x :) <$> opt xs
opt (Shl x : xs) = (ShiftL x :) <$> opt xs
opt (Prn : xs) = (Print :) <$> opt xs
opt (Inp : xs) = (Input :) <$> opt xs
opt [] = pure []

accum :: [AsmOp] -> [AsmOp]
accum (Add a : Add b : xs)
  | a + b > 127 = Add a : accum (Add b : xs)
  | otherwise = accum $ Add (a + b) : xs
accum (Sub a : Sub b : xs)
  | a + b > 127 = Sub a : accum (Sub b : xs)
  | otherwise = accum $ Sub (a + b) : xs
accum (ShiftL a : ShiftL b : xs)
  | a + b > 127 = ShiftL a : accum (ShiftL b : xs)
  | otherwise = accum $ ShiftL (a + b) : xs
accum (ShiftR a : ShiftR b : xs)
  | a + b > 127 = ShiftR a : accum (ShiftR b : xs)
  | otherwise = accum $ ShiftR (a + b) : xs
accum (x : xs) = x : accum xs
accum [] = []

header :: String
header = unlines
  [ ".text"
  , ".global main" 
  , ".global _tape"
  , ".lcomm _tape, 6400000"
  ,  "putval:"
  , "  movl $1, %eax"  
  , "  movl $1, %edi"
  , "  movq %r10, %rsi"
  , "  movl $1, %edx"
  , "  syscall"
  , "  ret"
  , "getval:" 
  , "  movl $0, %eax"
  , "  movl $0, %edi"
  , "  movq %r10, %rsi"
  , "  movl $1, %edx"
  , "  syscall"
  , "  ret" ]

toAsm :: AsmOp -> String
toAsm Clear = "  movb $0, (%r10)"
toAsm (Label x) = "begin_" ++ show x ++ ":\n  cmpb $0, (%r10)\n  jz end_" ++ show x
toAsm (EndLabel x) = "  cmpb $0, (%r10)\n  jnz begin_" ++ show x ++ "\nend_" ++ show x ++ ":"
toAsm (Add x) = "  addb $" ++ show x ++ ", (%r10)"
toAsm (Sub x) = "  subb $" ++ show x ++ ", (%r10)"
toAsm (ShiftR x) = "  addq $" ++ show x ++ ", %r10"
toAsm (ShiftL x) = "  subq $" ++ show x ++ ", %r10"
toAsm Print = "  call putval"
toAsm Input = "  call getval"

compile :: [AsmOp] -> String
compile c = header
         ++ "main:\n  movq _tape@GOTPCREL(%rip), %r10\n"
         ++ unlines (map toAsm c)
         ++ "  ret"

main :: IO ()
main = do
  file : r <- getArgs
  text <- readFile file
  let (_, parsed) = parse (text, [])
  optimized <- opt parsed
  let res = case r of
       ["-noopt"] -> optimized
       [] -> accum optimized
       _ -> error "unknown arguments"
  putStrLn $ compile res
