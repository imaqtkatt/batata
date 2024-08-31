inductive Vec (α : Type) : Nat → Type
| nil : Vec α Nat.zero
| cons (head : α) (tail : Vec α n) : Vec α (Nat.succ n)
deriving Repr

namespace Vec

def append {α : Type} (el : α) (v : Vec α n) : Vec α (Nat.succ n) :=
  match v with
  | .nil => .cons el .nil
  | .cons head tail => .cons head (Vec.append el tail)

def append_vec {α : Type} {m n : Nat} (v : Vec α m) (w : Vec α n) : Vec α (m + n) :=
  match v with
  | .nil => by
    have n := Nat.zero + n
    rw [Nat.zero_add]
    exact w
  | .cons head tail =>
    sorry

def length {α : Type} (_ : Vec α n) : Nat := n

def reverse {α : Type} (v : Vec α n) : Vec α n :=
  sorry

end Vec

theorem length_increases {v : Vec Unit n} : (Vec.append () v).length > n := by
  simp [Vec.append, Vec.length]
