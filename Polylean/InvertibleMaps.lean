universe u
variable {α : Type u}

structure InvertibleMap (α : Type u) where 
  fwd : α → α 
  inv : α → α
  left_inverse : inv ∘ fwd = id
  right_inverse : fwd ∘ inv = id
  


def inverse (f : InvertibleMap α) : InvertibleMap α :=
  ⟨f.inv, f.fwd, f.right_inverse, f.left_inverse⟩

def InvertibleMap.compose (f g : InvertibleMap α) : InvertibleMap α :=
  ⟨g.fwd ∘ f.fwd, f.inv ∘ g.inv, 
  by 
    apply funext
    intro x
    simp [Function.comp]
    let inner := congrFun g.left_inverse (f.fwd x)
    simp [Function.comp] at inner
    rw [inner]
    apply congrFun f.left_inverse, 
  by 
    apply funext
    intro x
    simp [Function.comp]
    let inner := congrFun f.right_inverse (g.inv x)
    simp [Function.comp] at inner
    rw [inner]
    apply congrFun g.right_inverse⟩
  
theorem eql_of_fwd_eql (f g : InvertibleMap α) : f.fwd = g.fwd → f = g := by
  intro hyp
  cases f with 
  | mk fwd₁ inv₁ left_inverse₁ right_inverse₁ =>
  cases g with
  | mk fwd₂ inv₂ left_inverse₂ right_inverse₂ => 
    have l₁ : fwd₁ = fwd₂ := hyp
    simp [l₁]
    apply funext
    intro x
    let l₂ := congrFun l₁ (inv₂ x)
    let l₃ := congrFun right_inverse₂ x
    simp [Function.comp] at l₃ 
    rw [l₃] at l₂
    let l₄ := congrArg inv₁ l₂
    let l₅ := congrFun left_inverse₁ (inv₂ x)    
    simp [Function.comp] at l₅
    rw [l₄] at l₅
    assumption
