structure PtltlCharStream = struct
  fun makeTokenStream charStream = 
    LrParser.Stream.streamify (PtltlChars.makeLexer charStream)
end
