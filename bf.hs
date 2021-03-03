import Text.Parsec
import System.IO

data BF = Op Char | Loop [BF]

run (Op '+' : xs) (l, i, r) = run xs (l, i + 1, r)
run (Op '-' : xs) (l, i, r) = run xs (l, i - 1, r)
run (Op '>' : xs) (l:ls, i, r) = run xs (ls, l, i:r)
run (Op '<' : xs) (l, i, r:rs) = run xs (i:l, r, rs)
run (Op '.' : xs) s@(_, i, _) = do putChar (toEnum i); hFlush stdout; run xs s
run (Op ',' : xs) (l, 0, r) = do c <- getChar; run xs (l, fromEnum c, r)
run (Loop _ : xs) s@(_, 0, _) = run xs s
run q@(Loop b : _) s = run b s >>= run q
run _ s = pure s

bfparse = many $ Op <$> oneOf "+-<>.," <|> Loop <$> (char '[' *> bfparse <* char ']')
main = do Right i <- parse bfparse [] <$> getLine; run i (repeat 0, 0, repeat 0)
