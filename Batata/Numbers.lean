-- inductive Nat
-- | succ : (pred : Num) → Num
-- | zero : Num



theorem one_eq_succ_zero : 1 = .succ .zero := rfl

theorem two_eq_succ_one : 2 = .succ 1 := rfl

theorem three_eq_succ_two : 3 = .succ 2 := rfl

theorem four_eq_succ_three : 4 = .succ 3 := rfl



theorem add_zero (a : Nat) : a + 0 = a := rfl

theorem add_succ (a b : Nat) : a + .succ b = .succ (a + b) := rfl

theorem succ_eq_add_one (n : Nat) : .succ n = n + 1 := rfl



-- ??????
theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero =>
    rw [add_zero]

  | succ m n =>
    rw [add_succ]
    rw [n]



theorem zero_add_2 (n : Nat) : 0 + n = n :=
  match n with
  | .zero => rfl
  | .succ pred =>
    congrArg Nat.succ (zero_add_2 pred)



theorem succ_add (a b : Nat) : (.succ a) + b = .succ (a + b) := by
  induction b with
  | zero =>
    rw [add_zero]
  | succ n ih =>
    rw [add_succ, add_succ]
    rw [ih]



theorem succ_add_2 {a b : Nat} : (.succ a) + b = .succ (a + b) :=
  match b with
  | .zero => rfl
  | .succ .. =>
    congrArg Nat.succ succ_add_2



theorem add_comm {a b : Nat} : a + b = b + a := by
  induction b with
  | zero =>
    rw [zero_add, add_zero]
  | succ p ih =>
    rw [succ_add, add_succ]
    rw [ih]



theorem add_comm_2 (a b : Nat) : a + b = b + a :=
  match b with
  | .zero =>
    Eq.symm (zero_add a)
  | .succ pred =>
    sorry



-- foo

inductive NumLe : Nat → Nat → Prop
| refl {n : Nat} : NumLe n n
| step {m n : Nat} (h : NumLe m n) : NumLe m (.succ n)



theorem zero_is_less_than_n (n : Nat) : NumLe .zero n :=
  -- foi intuitivo ter que fazer esse match
  match n with
  | .zero => .refl
  | .succ p => .step (zero_is_less_than_n p)



inductive NumLt : Nat → Nat → Prop where
| zero_lt_succ {n : Nat} : NumLt Nat.zero (Nat.succ n)
| succ_lt_succ {m n : Nat} (h : NumLt m n) : NumLt (Nat.succ m) (Nat.succ n)

example : Nat.zero = Nat.zero := rfl

example : NumLt .zero (.succ .zero) := .zero_lt_succ

example : NumLe .zero .zero := NumLe.refl

example : NumLe .zero (.succ .zero) :=
  NumLe.step (NumLe.refl)
