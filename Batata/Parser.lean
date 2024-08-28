structure Parser (α : Type) where
  runParser : List Char → Option (List Char × α)

def parseChar (c : Char) : Parser Char :=
  {
    runParser := λ
    | [] => Option.none
    | hd::tl =>
      if hd = c then
        Option.some (tl, hd)
      else
        Option.none
  }

def parseChar_o : Parser Char := parseChar 'o'

#eval Parser.runParser parseChar_o (String.toList "oi kkkk")

instance : Functor Parser where
  map f p :=
    {
      runParser := λinput => do
        let (rest, out) ← p.runParser input
        pure (rest, f out)
    }

def ignored (p : Parser α) := Functor.mapConst () p

def parseChar_o_to_nat : Parser Nat := Char.toNat <$> parseChar_o

instance : Applicative Parser where
  pure x :=
    {
      runParser := λinput => pure (input, x)
    }

  seq f u :=
    let f₁ := f.runParser
    let f₂ := u ()
    {
      runParser := λinput =>
        do
          let (rest, f) ← f₁ input
          let (rest', out) ← f₂.runParser rest
          pure (rest', f out)
    }

instance : Monad Parser where
  bind p f :=
    {
      runParser := λinput =>
        do
          let (rest, p') <- p.runParser input
          let p'' := f p'
          p''.runParser rest
    }

def parse_o_then_i := parseChar 'o' *> parseChar 'i'

#eval Parser.runParser parse_o_then_i (String.toList "oi kkk")

#eval Parser.runParser parseChar_o_to_nat (String.toList "oi kkkk")

def parseSpan (p : Char → Bool) : Parser (List Char) :=
  {
    runParser := λinput =>
      let (got, rest) := List.span p input
      pure (rest, got)
  }

def notEmpty (parser : Parser (List α)) : Parser (List α) :=
  {
    runParser := λinput =>
      match parser.runParser input with
      | Option.none => Option.none
      | Option.some (_, []) => Option.none
      | Option.some (rest, out) => Option.some (rest, out)
  }

def parseWhitespace : Parser (List Char) := parseSpan (.= ' ')
def parseWhitespaceIgnored : Parser Unit := ignored (parseSpan (.= ' '))

def listTraverse [Monad m] (f : α → m β) : List α → m (List β)
  | [] => pure []
  | hd::xs => do
    let y ← f hd
    let ys ← listTraverse f xs
    pure (y :: ys)

def parseString s := listTraverse parseChar (String.toList s)

#eval Parser.runParser parseWhitespaceIgnored (String.toList "   aa oi")

#eval Parser.runParser (parseString "batata") (String.toList "batata palha")
