class SMul (α : Type u) (β : Type v)  where
  sMul : α → β → β 

infixl:70 " • "   =>  SMul.sMul
 