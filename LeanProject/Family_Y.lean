import Mathlib
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.Basic

/-!
Construction on Family Y
-/

namespace Family_Y_n_k



def RowVector (n : ℕ) (α : Type) : Type := Fin n → α


def Row0 (k : ℕ) : RowVector (2 * (2 * k + 1)) ℤ := fun i =>
  let n := (2 * (2 * k + 1))
  if i.val == 0 then
    0
  else if i.val == 1 then
    2
  else if i.val < n / 2 then
    1
  else
    -1



def Row1 (k : ℕ) : RowVector (2 * (2 * k + 1)) ℤ := fun i =>
  let n := (2 * (2 * k + 1))
  if i.val == 0 then
    -2
  else if i.val == 1 then
    0
  else if i.val < (n / 2 +2) then
    1
  else
    -1



def T (k : ℕ) {α : Type} (v : RowVector (2 * (2 * k + 1)) α) : RowVector (2 * (2 * k + 1)) α :=
  fun i => v (i - 1)

-- here Fin n type is of modulo operation hence i+1 := ⟨ (i.val mod n)+1, proof⟩

#eval List.ofFn (Row0 2)
#eval List.ofFn (T 2  (Row0 2))
#eval List.ofFn (Row1 2)
#eval List.ofFn (T 2  (Row1 2))

def useT (k : ℕ) {α : Type} : ℕ → RowVector (2 * (2 * k + 1)) α → RowVector (2 * (2 * k + 1)) α :=
  fun m v  => match m, v with
  | 0 ,    v => v
  | m+1,  v => T k (useT k m v)

#eval List.ofFn (useT 1 2 (Row0 1))
#eval List.ofFn (Row1 1)
#eval List.ofFn (useT 1 2 (Row1 1))


def Row_Periodic (k : ℕ) : ℕ → RowVector (2 * (2 * k + 1)) ℤ
    | 0    => Row0 k
    | 1    => Row1 k
    | i+2  => useT k 2 (Row_Periodic k i)


-- k is defined to be the size of row, second number n ∈ ℕ  should be the n^{th} row of the matrix

#eval List.ofFn (Row_Periodic 1 0)
#eval List.ofFn (Row_Periodic 1 1)
#eval List.ofFn (Row_Periodic 1 2)
#eval List.ofFn (Row_Periodic 1 3)
#eval List.ofFn (Row_Periodic 1 4)
#eval List.ofFn (Row_Periodic 1 5)

def Matrix (m n : ℕ) (α : Type) := Fin m → RowVector n α
-- here n should be the column index, and m should be the row index


def Y (k : ℕ) : Matrix (2 * (2 * k + 1)) (2 * (2 * k + 1)) ℤ :=
  fun i => Row_Periodic k i.val
-- we map the row index to corresponding to each row to get the matrix

#eval Y 1



--To make matrix more readable, below i asked AI to re-format the matrix
-- Helper function to safely convert a Fin function into a List
def finToList {α : Type} {n : Nat} (f : Fin n → α) : List α :=
  match n with
  | 0 => []
  | n + 1 => f 0 :: finToList (fun i => f i.succ)

-- Custom pretty-printer instance using standard Lean Std.Format
instance [Repr α] {m n : Nat} : Repr (Matrix m n α) where
  reprPrec M _ :=
    let rows := finToList (fun i =>
      let rowVec : RowVector n α := M i
      let rowElems := finToList (fun j => repr (rowVec j))
      Std.Format.text "  [" ++ Std.Format.joinSep rowElems ", " ++ Std.Format.text "]"
    )
    let body := Std.Format.joinSep rows (Std.Format.text "," ++ Std.Format.line)
    Std.Format.text "[" ++ Std.Format.line ++ body ++ Std.Format.line ++ Std.Format.text "]"


#eval IO.println (repr (Y 1))

end Family_Y_n_k
