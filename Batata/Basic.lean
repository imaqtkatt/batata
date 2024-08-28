--prelude



inductive LList (α : Type)
| nil
| cons (head : α) (tail : LList α)
deriving Repr


namespace LList

def append {α : Type} (a b : LList α) :=
  match a with
  | .nil => b
  | .cons head tail => .cons head (append tail b)

#eval append (.cons 1 (.cons 3 .nil)) (.cons 2 .nil)

def reverse {α : Type} (a : LList α) : LList α :=
  match a with
  | .nil => .nil
  | .cons head tail => (append (reverse tail) (.cons head .nil))

#eval reverse (.cons 3 (.cons 2 (.cons 1 .nil)))

theorem rev_of_append_cons {α : Type} (a : LList α) (b : α) :
  reverse (append a (.cons b .nil)) = .cons b (reverse a) :=
  match a with
  | .nil => by
    rfl
  | .cons head tail => by
    simp [append, reverse]
    sorry

theorem list_append_nil_useless {α : Type} (a : LList α) :
  a = append a .nil :=
  match a with
  | .nil => rfl
  | .cons head tail => by
    simp [append]
    exact list_append_nil_useless tail

theorem rev_of_append_eq_rev_append_rev {α : Type} (a b : LList α) :
  reverse (append a b) = append (reverse b) (reverse a) :=
  match a with
  | .nil => by
    simp [append, reverse]
    exact list_append_nil_useless b.reverse
  | .cons head tail => by
    simp [reverse, append]
    sorry

theorem rev_of_rev_eq_sefl {α : Type} (a : LList α) : reverse (reverse a) = a :=
  match a with
  | .nil => rfl
  | .cons head tail => by
    simp [reverse]
    rw [rev_of_append_eq_rev_append_rev (reverse tail) (.cons head .nil)]
    simp [reverse, append]
    exact rev_of_rev_eq_sefl tail
