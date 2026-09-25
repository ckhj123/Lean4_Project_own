import Mathlib
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.Basic

namespace Family_Y_n_k



def RowVector (n : Nat) (α : Type) := Fin n → α


def Row0 (k : Nat) : RowVector (2 * (2 * k + 1)) Int := fun i =>
  let n := (2 * (2 * k + 1))
  if i.val == 0 then
    0
  else if i.val == 1 then
    2
  else if i.val < n / 2 then
    1
  else
    -1

def Row1 (k : Nat) : RowVector (2 * (2 * k + 1)) Int := fun i =>
  let n := (2 * (2 * k + 1))
  if i.val == 0 then
    -2
  else if i.val == 1 then
    0
  else if i.val < (n / 2 -2) then
    1
  else
    -1





end Family_Y_n_k
