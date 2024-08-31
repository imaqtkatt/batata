inductive Vec (α : Type) : Nat → Type
| nil : Vec α Nat.zero
| cons (head : α) (tail : Vec α n) : Vec α (Nat.succ n)
deriving Repr

namespace Vec

def append_el {α : Type} (el : α) (v : Vec α n) : Vec α (Nat.succ n) :=
  match v with
  | .nil => .cons el .nil
  | .cons head tail => .cons head (append_el el tail)

def append {α : Type} {m n : Nat} (v : Vec α m) (w : Vec α n) : Vec α (m + n) :=
  match v with
  | .nil => by
    rw [Nat.zero_add]
    exact w
  | .cons head tail => by
    rw [Nat.succ_add_eq_add_succ]
    exact .cons head (append tail w)

def length {α : Type} (_ : Vec α n) : Nat := n

def reverse {α : Type} : Vec α n → Vec α n
  | .nil => .nil
  | .cons head tail => by
    rw [Nat.succ_eq_one_add]
    exact append (Vec.cons head .nil) (reverse tail)

end Vec

-- catapimbas
-- #eval Vec.reverse (Vec.append_el 2 (Vec.append_el 1 .nil))

theorem length_increases {v : Vec Unit n} : (Vec.append_el () v).length > n := by
  simp [Vec.append_el, Vec.length]

theorem rev_rev {α : Type} {n : Nat} {v : Vec α n} : v.reverse.reverse = v := by
  induction v with
  | nil =>
    simp [Vec.reverse]
  | cons head tail =>
    simp [Vec.reverse]
    sorry
