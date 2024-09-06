inductive Vec (α : Type) : Nat → Type
| nil : Vec α Nat.zero
| cons (head : α) (tail : Vec α n) : Vec α (Nat.succ n)
deriving Repr

namespace Vec

def append_el {α : Type} (v : Vec α n) (el : α) : Vec α (Nat.succ n) :=
  match v with
  | .nil => .cons el .nil
  | .cons head tail => .cons head (append_el tail el)

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
    append_el (reverse tail) head

end Vec

instance {m n : Nat} {α : Type} : HAppend (Vec α m) (Vec α n) (Vec α (m + n)) where
  hAppend := Vec.append

-- catapimbas
-- #eval Vec.reverse (Vec.append_el 2 (Vec.append_el 1 .nil))

theorem length_increases {v : Vec Unit n} : (Vec.append_el v ()).length > n := by
  simp [Vec.append_el, Vec.length]

@[simp] theorem append_nil {a : Vec α m} : a.append .nil = a  :=
  match a with
  | .nil => rfl
  | .cons .. => by
    simp [Vec.append]
    exact append_nil

@[simp] theorem nil_append {α : Type} {n : Nat} {a : Vec α n} :
  Vec.nil.append a = by {simp [Nat.add]; exact a} := rfl

@[simp] theorem rev_single {α : Type} {x : α} : (Vec.cons x Vec.nil :Vec α 1).reverse = (Vec.cons x Vec.nil) := by
  simp [Vec.reverse, Vec.append_el]

@[simp] theorem rev_nil {α : Type} : (Vec.nil : Vec α 0).reverse = Vec.nil := by
  rw [Vec.reverse]

@[simp] theorem rev_cons {α : Type} {n : Nat} (x : α) (v : Vec α n) :
  (Vec.cons x v).reverse = v.reverse.append_el x := by
    simp [Vec.reverse]

@[simp] theorem cons_append_el {α : Type} {n : Nat} (x : α) (v : Vec α n) (y : α) :
  (Vec.cons x v).append_el y = Vec.cons x (v.append_el y) := by
    simp [Vec.append_el]

theorem rev_append_el {α : Type} {n : Nat} (v : Vec α n) (x : α) :
  (v.append_el x).reverse = Vec.cons x v.reverse := by
    induction v with
    | nil =>
      simp [Vec.append_el]
    | cons head tail =>
      simp [Vec.append_el]
      sorry

theorem rev_append_rev_rev {α : Type} {m n : Nat} (a : Vec α m) (b : Vec α m) :
  Vec.reverse (Vec.append a b) = Vec.append (Vec.reverse b) (Vec.reverse a) := by
  induction a with
  | nil =>
    simp [Vec.append, Vec.reverse]
  | cons head tail i =>
    simp [Vec.reverse]
    simp [Vec.append]
    sorry

theorem rev_tail_append_head_rev {α : Type} {m : Nat} {head : α} {tail : Vec α m} :
  (tail.reverse.append_el head).reverse = Vec.cons head tail := by
  induction tail with
  | nil =>
    simp [Vec.append]
    simp [Vec.append_el]
  | cons hd tl h =>
    simp [Vec.reverse]
    sorry

theorem rev_rev {α : Type} {n : Nat} {v : Vec α n} : v.reverse.reverse = v := by
  induction v with
  | nil =>
    simp [Vec.reverse]
  | cons head tail =>
    simp [Vec.reverse]
    exact rev_tail_append_head_rev

-- #eval
--   let tail := (Vec.cons 3 (Vec.cons 4 Vec.nil));
--   (tail.reverse ++ (Vec.cons 1 .nil)).reverse

-- #eval (Vec.cons 1 (Vec.reverse (.cons 2 (.cons 3 .nil)))).reverse
-- #eval (Vec.cons 1 (Vec.reverse (.cons 2 (.cons 3 (.cons 4 .nil))))).reverse

-- rev (cons head (rev tail)) = cons head tail
