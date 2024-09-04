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
  | .cons head tail =>
    append (reverse tail) (Vec.cons head .nil)

end Vec

instance {m n : Nat} {α : Type} : HAppend (Vec α m) (Vec α n) (Vec α (m + n)) where
  hAppend := Vec.append

-- catapimbas
-- #eval Vec.reverse (Vec.append_el 2 (Vec.append_el 1 .nil))

theorem length_increases {v : Vec Unit n} : (Vec.append_el () v).length > n := by
  simp [Vec.append_el, Vec.length]

@[simp] theorem append_nil {a : Vec α m} : a.append .nil = a  :=
  match a with
  | .nil => rfl
  | .cons .. => by
    simp [Vec.append, List.append_nil]
    exact append_nil

@[simp] theorem nil_append {α : Type} {n : Nat} {a : Vec α n} :
  Vec.nil.append a = by {simp [Nat.add]; exact a} := rfl

@[simp] theorem rev_single {α : Type} {a : Vec α 1} : a.reverse = a := by
  cases a
  case cons head tail =>
    cases tail
    case nil =>
      simp [Vec.reverse, Vec.append]

@[simp] theorem rev_single_ {α : Type} {el : α} : (Vec.cons el .nil).reverse = Vec.cons el .nil := by
  exact rev_single

theorem rev_append_rev_rev {α : Type} {m n : Nat} (a : Vec α m) (b : Vec α m) :
  Vec.reverse (Vec.append a b) = Vec.append (Vec.reverse b) (Vec.reverse a) := by
  induction b with
  | nil =>
    simp [Vec.append, Vec.reverse]
  | cons head tail i =>
    simp [Vec.reverse, Vec.append]
    sorry

theorem rev_tail_append_head_rev {α : Type} {m : Nat} {head : α} {tail : Vec α m} :
  (tail.reverse.append (Vec.cons head .nil)).reverse = Vec.cons head tail := by
  induction tail with
  | nil =>
    simp [Vec.reverse]
  | cons hd tl =>
    simp [Vec.reverse]
    sorry

theorem rev_rev {α : Type} {n : Nat} {v : Vec α n} : v.reverse.reverse = v := by
  induction v with
  | nil =>
    simp [Vec.reverse]
  | cons head tail =>
    simp [Vec.reverse, Vec.append]
    exact rev_tail_append_head_rev

-- #eval
--   let tail := (Vec.cons 3 (Vec.cons 4 Vec.nil));
--   (tail.reverse ++ (Vec.cons 1 .nil)).reverse

-- #eval (Vec.cons 1 (Vec.reverse (.cons 2 (.cons 3 .nil)))).reverse
-- #eval (Vec.cons 1 (Vec.reverse (.cons 2 (.cons 3 (.cons 4 .nil))))).reverse

-- rev (cons head (rev tail)) = cons head tail
