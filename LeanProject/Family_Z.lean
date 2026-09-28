import Mathlib
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.Basic


/-!
Construction on Family Z
-/


namespace Family_Z_n_k

def RowVector (n : ℕ) (α : Type) : Type := Fin n → α

def Row0 (k : ℕ) : RowVector (5 * (2 * k + 1)) ℤ := fun i =>
  let n := (5 * (2 * k + 1))
  if i.val == 0 then
    0
  else if i.val < ((n-1) / 2) + 1 then
    1
  else
    -1

#eval (Row0 1)

def Row1 (k : ℕ) : RowVector (5 * (2 * k + 1)) ℤ := fun i =>
  let n := (5 * (2 * k + 1))
  if i.val == 0 then
    -1
  else if i.val == 1 then
    0
  else if i.val == 2 then
    2
  else if i.val == 3 then
    2
  else if i.val < ((n-1) / 2) + 1 then
    1
  else
    -1

#eval (Row1 1)


def Row2 (k : ℕ) : RowVector (5 * (2 * k + 1)) ℤ := fun i =>
  let n := (5 * (2 * k + 1))
  if i.val == 0 then
    -1
  else if i.val == 1 then
    -2
  else if i.val == 2 then
    0
  else if i.val == 3 then
    2
  else if i.val < ((n - 1) / 2) + 3 then
    1
  else
    -1

#eval (Row2 1)

def Row3 (k : ℕ) : RowVector (5 * (2 * k + 1)) ℤ := fun i =>
  let n := (5 * (2 * k + 1))
  if i.val == 0 then
    -1
  else if i.val == 1 then
    -2
  else if i.val == 2 then
    -2
  else if i.val == 3 then
    0
  else if i.val < ((n - 1) / 2) + 5 then
    1
  else
    -1

#eval (Row3 1)

def Row4 (k : ℕ) : RowVector (5 * (2 * k + 1)) ℤ := fun i =>
  let n := (5 * (2 * k + 1))
  if i.val == 0 then
    -1
  else if i.val == 1 then
    -1
  else if i.val == 2 then
    -1
  else if i.val == 3 then
    -1
  else if i.val == 4 then
    0
  else if i.val < ((n - 1) / 2) + 5 then
    1
  else
    -1

#eval (Row4 1)

def T (k : ℕ) {α : Type} (v : RowVector (5 * (2 * k + 1)) α) : RowVector (5 * (2 * k + 1)) α :=
  fun i => v (i - 1)



def useT (k : ℕ) {α : Type} : ℕ → RowVector (5 * (2 * k + 1)) α → RowVector (5 * (2 * k + 1)) α :=
  fun m v  => match m, v with
  | 0 ,    v => v
  | m+1,  v => T k (useT k m v)

def Row_Periodic (k : ℕ) : ℕ → RowVector (5 * (2 * k + 1)) ℤ
    | 0    => Row0 k
    | 1    => Row1 k
    | 2    => Row2 k
    | 3    => Row3 k
    | 4    => Row4 k
    | i+5  => useT k 5 (Row_Periodic k i)

#eval (Row_Periodic 1 5)
#eval (Row_Periodic 1 6)
#eval (Row_Periodic 1 7)
#eval (Row_Periodic 1 8)
#eval (Row_Periodic 1 9)


def Matrix (m n : ℕ) (α : Type) := Fin m → RowVector n α


def Z (k : ℕ) : Matrix (5 * (2 * k + 1)) (5 * (2 * k + 1)) ℤ :=
  fun i => Row_Periodic k i.val


#eval Z 1


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


#eval IO.println (repr (Z 1))

end Family_Z_n_k
