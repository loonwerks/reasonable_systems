structure PtltlToken = struct

  open PtltlTokens.Tokens
  open PtltlTokens.ParserData.Token

  fun toString (TOKEN (term, _)) = PtltlTokens.ParserData.EC.showTerminal term 

  fun format tok = let
    val TOKEN (term, (_, lp, cp)) = tok
    val bigString = concat [
      Int.toString lp, ":", Int.toString cp, " ",
      (toString tok)]
    in bigString
    end

  fun isEOF tok =
    (toString tok) = "EOF"

end
