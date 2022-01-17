open import Data.List.Base using (List; foldr)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc; z≤n; s≤s; _<_; _<ᵇ_)
open import Data.Bool.Base using (Bool; false; true; not)


data Bin : Set where
   Z : Bin
   U : Bin
   
id : {A : Set} -> A -> A
id x = x

count_Z : List(Bin) -> ℕ 
count_Z = foldr (λ {Z -> suc; U -> id}) 0

count_U : List(Bin) -> ℕ 
count_U = foldr (λ {Z -> id; U -> suc}) 0

most_present : List(Bin) -> Bin
most_present l with (count_Z l <ᵇ count_U l)
... | false = U
... | true = Z