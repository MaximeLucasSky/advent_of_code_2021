
open import Agda.Builtin.Nat using (_-_; _*_)
open import Data.Nat.Base as ℕ using (ℕ; _+_)
open import Data.Product using (_×_; _,_)
open import Data.List using (List; foldr)


data Command : Set where
  fwd : ℕ -> Command
  down : ℕ -> Command
  up : ℕ -> Command

Position : Set 
Position = ℕ × ℕ

follow-command : Command -> Position -> Position
follow-command (fwd x) (depth , pos) = (depth , pos + x)
follow-command (down x) (depth , pos) = (depth + x , pos)
follow-command (up x) (depth , pos) = (depth - x , pos)

follow-commands : List (Command) -> Position 
follow-commands l = foldr (follow-command) (0 , 0) l

solution : List (Command) -> ℕ
solution l with (follow-commands l) 
... | depth , pos = depth * pos


