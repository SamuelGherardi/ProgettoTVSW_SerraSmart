//ASM MINIMALE per il funzionamento del model checker e del model advisor
asm SerraSmartMinimal

import ../STDL/StandardLibrary
import ../STDL/CTLLibrary
import ../STDL/LTLLibrary

signature:

// Domini semplici (solo enum e boolean)
enum domain Luce = {LUCE1 | LUCE2}
enum domain StatoLuce = {ON | OFF}

controlled statoLuce : Luce -> StatoLuce
derived luceAccesa : Boolean

definitions:

function luceAccesa = (exist $l in Luce with statoLuce($l) = ON)

rule r_accendi =
    forall $l in Luce do
        statoLuce($l) := ON

main rule r_Main = 
if(not luceAccesa)then r_accendi[]
endif

default init s0:
    function statoLuce($l in Luce) = OFF
