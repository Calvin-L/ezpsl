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

globalsScratchVar :: String
globalsScratchVar = "_globalsScratch"

initialPc :: String
initialPc = "_begin"

selfConstant :: String
selfConstant = "self"

undefinedConstant :: String
undefinedConstant = "_Undefined"
