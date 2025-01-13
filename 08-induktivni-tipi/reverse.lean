def vsota : List Int → Int :=
  fun xs =>
    match xs with
    | .nil => 0
    | .cons x xs => x + vsota xs

def aux : List Int → Int → Int :=
  fun xs => fun acc =>
    match xs with
    | .nil => acc
    | .cons x xs => aux xs (acc + x)

def vsota' : List Int → Int :=
  fun xs => aux xs 0

theorem aux_in_plus : ∀ xs, ∀ acc, x + aux xs acc = aux xs (acc + x) :=
  by
    intros xs
    induction xs with
    | nil => sorry
    | cons x' xs' ih =>
        intro acc
        calc
          x + aux (x' :: xs') acc
          = x + aux xs' (acc + x') := by simp [aux]
          _ = aux xs' ((acc + x') + x) := by rw [ih]
          _ = aux xs' ((acc + x) + x') := by sorry -- nekaj z Nat.
          _ = aux (x' :: xs') (acc + x) := by simp [aux]

theorem vsoti_sta_enaki : vsota xs = vsota' xs :=
  by
    induction xs with
    | nil => simp [vsota, vsota', aux]
    | cons x xs' ih =>
        calc
          vsota (x :: xs')
          = x + vsota xs' := by simp [vsota]
          _ = x + vsota' xs' := by rw [ih]
          _ = x + aux xs' 0 := by simp [vsota']
          _ = aux xs' x := by rw [aux_in_plus]
          _ = aux (x :: xs') 0 := by simp [aux]
          _ = vsota' (x :: xs') := by simp [vsota']



def reverse {A : Type} : List A -> List A :=
  fun xs =>
    match xs with 
    | [] => []
    | y :: ys => reverse (ys) ++ [y]

def reverseAux {A : Type} : List A -> List A -> List A :=
  fun xs acc =>
    match xs with
    | [] => acc
    | y :: ys => reverseAux ys (y :: acc)

def reverse' {A : Type} : List A -> List A :=
  fun xs =>
    reverseAux xs []

theorem pomozna {A : Type} : ∀ {lst : List A}, ∀ {acc : List A}, reverseAux lst acc = (reverse lst) ++ acc :=
   by 
    intro lst
    induction lst with
    | nil =>
      intro acc
      simp [reverse, reverseAux]
    | cons x xs ih =>
      intro acc 
      simp[reverse, reverseAux]
      rw [ih]
theorem lema1 {A : Type} {xs : List A} : xs ++ [] = xs :=
  by 
    induction xs with
    | nil => 
      simp
    |cons x xs ih =>
      simp

theorem enaka {A : Type}{xs : List A} : reverse xs = reverse' xs :=
  by 
    rw [reverse']
    rw [pomozna]
    rw [lema1]
    
