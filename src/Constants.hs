module Constants where

startOfFileInclude :: String
startOfFileInclude = "\\* #include "

endOfFileInclude :: String
endOfFileInclude = "\\* /include "

pcVar :: String
pcVar = "_pc"

framesVar :: String
framesVar = "_frames"

retVar :: String
retVar = "_ret"

actorVar :: String
actorVar = "_actor"

selfConstant :: String
selfConstant = "self"

undefinedConstant :: String
undefinedConstant = "_Undefined"
