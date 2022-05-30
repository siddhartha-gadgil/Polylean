/-- Scalar multiplication, specialized form of `HMul` for using a different symbol and easier type inference -/
class SMul (α : Type u) (β : Type v)  where
  sMul : α → β → β 

infixl:70 " • "   =>  SMul.sMul
 