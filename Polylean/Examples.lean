import Polylean.Length
import Polylean.LengthBound
open Letter

#eval (Word.wrd ([α, α, β, α!, α,  β!])).splits (1)

#eval (Word.wrd ([α, α, β, α!, α,  β!])).length

#eval (Word.wrd ([α, α, β, α!, β!])).length

#eval wordLength ([α, α, β, α!, β!])

#eval wordLength ([α, α, β, α!, β!]^ 3)

