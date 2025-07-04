asm SerraSmart

import ../STDL/StandardLibrary
import ../STDL/CTLLibrary
import ../STDL/LTLLibrary

signature:
	// DOMINI
	// Domini rappresentanti gli elementi della SerraSmart e lo stato degli elementi
	domain Luci subsetof Integer
	domain Irrigatori subsetof Integer
	domain LivelloIrrigatore subsetof Integer
	domain Temperatura subsetof Integer
	domain Umidita subsetof Integer
	domain Luminosita subsetof Integer
	enum domain Ventilatori = {PRINCIPALE | SECONDARIO}
	enum domain StatoVentilatore = {ACCESO | SPENTO}
	enum domain StatoLuce = {ON | OFF}
	enum domain ModalitaControllo = {MANUALE | AUTOMATICA}
	
	// Domini per le funzioni monitorate (input dall'environment)
	enum domain Elementi = {SERRA | LUCI | IRRIGATORI | VENTILATORI /* | ANTIFURTO*/}
	enum domain AzioniSerra = {CHIUDI_TUTTO | APRI_TUTTO}
	enum domain AzioniLuci = {ACCENDI_LUCE | SPEGNI_LUCE}
	enum domain AzioniIrrigatori = {IMPOSTA_IRRIGATORE | APRI_IRRIGATORE | CHIUDI_IRRIGATORE}
	enum domain AzioniVentilatori = {ACCENDI_VENTILATORE | SPEGNI_VENTILATORE}
	
	// FUNZIONI
	controlled statoLuce: Luci -> StatoLuce
	controlled statoIrrigatore: Irrigatori -> LivelloIrrigatore
	controlled statoVentilatore: Ventilatori -> StatoVentilatore
	controlled luminositaAttuale : Integer
	controlled temperaturaAttuale : Integer
	controlled umiditaAttuale : Integer
	
	monitored elemento: Elementi
	monitored azioneSerra: AzioniSerra
	monitored azioneLuci: AzioniLuci
	monitored azioneIrrigatori: AzioniIrrigatori
	monitored azioneVentilatori: AzioniVentilatori
	monitored luce: Luci
	monitored irrigatore: Irrigatori
	monitored ventilatore: Ventilatori
	monitored livello_irrigatore: LivelloIrrigatore
	monitored sogliaTempMin : Integer
	monitored sogliaTempMax : Integer
	monitored sogliaUmiditaMin : Integer
	monitored sogliaUmiditaMax : Integer
	monitored sogliaLuceMin : Integer
	monitored sogliaLuceMax : Integer
	monitored sceltaModalita : ModalitaControllo
	
	derived serraChiusa: Boolean //True se la serra ha luci spente, irrigatori spenti e ventilatori spenti
	
	
definitions:
	// DEFINIZIONE DOMINI
	domain Luci = {1 : 5}
	domain Irrigatori = {1 : 3}
	domain LivelloIrrigatore = {0 : 100} //0% = completamente chiuso; 100% = completamente aperto
	domain Temperatura = {1:100} //per modellare la temperatura rilevata
	domain Umidita = {1:100} //per modellare l'umidità rilevata
	domain Luminosita = {1:100} //per modellare la luminosità rilevata
	
	// DEFINIZIONE FUNZIONI	
	function serraChiusa = 	(forall $l in Luci with statoLuce($l) = OFF) and
							(forall $i in Irrigatori with statoIrrigatore($i) = 0) and
							(forall $v in Ventilatori with statoVentilatore($v) = SPENTO)
	
	
	// DEFINIZIONE DELLE REGOLE
	// Regola che va ad accendere oppure a spegnere una singola luce della serra
	rule r_luci($azione in AzioniLuci) = 
		if ($azione = ACCENDI_LUCE)	
		then statoLuce(luce) := ON
		else 	if ($azione = SPEGNI_LUCE)
				then statoLuce(luce) := OFF
				endif
		endif
	
	// Regola che va ad accendere oppure a spegnere un singolo ventilatore all'interno della serra
	rule r_ventilatori($azione in AzioniVentilatori) = 
		if ($azione = ACCENDI_VENTILATORE)	
		then statoVentilatore(ventilatore) := ACCESO
		else 	if ($azione = SPEGNI_VENTILATORE)
				then statoVentilatore(ventilatore) := SPENTO
				endif
		endif
		
	// Regola che va ad accendere oppure a spegnere un singolo irrigatore all'interno della serra
	rule r_irrigatori($azione in AzioniIrrigatori) =
		par
		if ($azione = IMPOSTA_IRRIGATORE)	
		then statoIrrigatore(irrigatore) := livello_irrigatore
		endif
		if ($azione = APRI_IRRIGATORE)
		then statoIrrigatore(irrigatore) := 100
		endif
		if ($azione = CHIUDI_IRRIGATORE)
		then statoIrrigatore(irrigatore) := 0
		endif
		endpar
	
	// Regola che va ad accendere tutte le luci nel momento in cui la luminosità segnalata è minore della soglia minima
	rule r_luciAccese($azione in AzioniLuci) = 
		forall $l in Luci with statoLuce($l) = OFF
		do
			statoLuce($l) := ON
	
	// Regola che va ad spegnere tutte le luci nel momento in cui la luminosità segnalata è maggiore della soglia massima
	rule r_luciSpente($azione in AzioniLuci) = 
		forall $l in Luci with statoLuce($l) = ON
		do
			statoLuce($l) := OFF
	
	// Regola che va ad accendere tutti i ventilatori nel momento in cui la temperatura segnalata è maggiore della soglia massima
	rule r_ventilatoriAccesi($azione in AzioniVentilatori) = 
		forall $v in Ventilatori with statoVentilatore($v) = SPENTO
		do
			statoVentilatore($v) := ACCESO
	
	// Regola che va a spegnere tutti i ventilatori nel momento in cui la temperatura segnalata è sotto la soglia minima
	rule r_ventilatoriSpenti($azione in AzioniVentilatori) = 
		forall $v in Ventilatori with statoVentilatore($v) = ACCESO
		do
			statoVentilatore($v) := SPENTO
	
	// Regola che va ad accendere tutti gli irrigatori nel momento in cui l'umidità segnalata è sotto la soglia minima
	rule r_irrigatoriAccesi($azione in AzioniIrrigatori) = 
		forall $i in Irrigatori with statoIrrigatore($i) !=100
		do
			statoIrrigatore($i) := 100
	
	// Regola che va a spegnere tutti gli irrigatori nel momento in cui l'umidità segnalata è sopra la soglia massima
	rule r_irrigatoriSpenti($azione in AzioniIrrigatori) = 
		forall $i in Irrigatori with statoIrrigatore($i) !=0
		do
			statoIrrigatore($i) := 0
							
	
	
	// PROPRIETA'
	//CTL 1 – Liveness: se la temperatura supera la soglia, prima o poi si attiva uno dei due ventilatori
	CTLSPEC ag ((temperaturaAttuale > sogliaTempMax) implies af (statoVentilatore(PRINCIPALE) = ACCESO or statoVentilatore(SECONDARIO) = ACCESO ))
	
	//CTL 2 – Safety: non devono essere accesi contemporaneamente tutti gli attuatori in qualsiasi momento
	CTLSPEC not ag(
    (exist $l in Luci with statoLuce($l) = ON) and
    (exist $i in Irrigatori with statoIrrigatore($i) > 0) and
    (exist $v in Ventilatori with statoVentilatore($v) = ACCESO))
    
    //LTL 1 – Until: le luci rimangono accese fino a quando la luce non supera la soglia
	LTLSPEC g ((luminositaAttuale < sogliaLuceMin) implies u(statoLuce(1) = ON, luminositaAttuale > sogliaLuceMin))
	
	//LTL 2 – Globale: se la serra è chiusa, nessun attuatore deve essere attivo
	LTLSPEC g (
    serraChiusa implies
    (forall $l in Luci with statoLuce($l) = OFF) and
    (forall $i in Irrigatori with statoIrrigatore($i) = 0) and
    (forall $v in Ventilatori with statoVentilatore($v) = SPENTO)
    )
	


	
	// REGOLA PRINCIPALE
	main rule r_Main =
	par
	
	if(sceltaModalita = AUTOMATICA) then // Se la scelta è il controllo automatico della serra
	par	// Si simula in modo casuale il livello di luminosità presente nella serra
		choose $x in Luminosita with true
		do
			par
			luminositaAttuale:=$x
			if ($x < sogliaLuceMin)// Se la luminosità risulta sotto la soglia minima si vanno ad accedendere tutte le luci
			then r_luciAccese[azioneLuci]
			endif
			if ($x > sogliaLuceMax)// Se la luminosità risulta sopra la soglia massima si vanno ad spegnere tutte le luci
			then r_luciSpente[azioneLuci]
			endif
			endpar
		
		// Si simula in modo casuale il livello di temperatura presente nella serra
		choose $t in Temperatura with true
		do
			
			par
			temperaturaAttuale:=$t
			if ($t < sogliaTempMin)// Se la temperatura risulta sotto la soglia minima si vanno ad accedendere tutte le luci e spegnere eventuali ventilatori accesi
			then
				par
				r_luciAccese[azioneLuci]
				r_ventilatoriSpenti[azioneVentilatori]
				endpar
			endif
			if ($t > sogliaTempMax)// Se la temperatura risulta sopra la soglia massima si vanno ad accedendere tutti i ventilatori
			then r_ventilatoriAccesi[azioneVentilatori]	
			endif
			endpar
			
		choose $u in Umidita with true
		do
			par
			umiditaAttuale:=$u
			if ($u < sogliaUmiditaMin)// Se l'umidità risulta sotto la soglia minima si vanno ad accedendere gli irrigatori al massimo
			then r_irrigatoriAccesi[azioneIrrigatori]
			endif
			if ($u > sogliaUmiditaMax)// Se l'umidità risulta sopra la soglia massima si vanno a spegnere tutti gli irrigatori
			then r_irrigatoriSpenti[azioneIrrigatori]
			endif
			endpar
		
	endpar				 
	endif
	
	if(sceltaModalita = MANUALE)then // Se la scelta è il controllo manuale della serra
		par
		choose $z in Luminosita with true // Si imposta una delle luci
		do
			par
			luminositaAttuale:=$z
			r_luci[azioneLuci]
			endpar
		choose $w in Temperatura with true // Si imposta uno dei ventilatori
		do
			par
			temperaturaAttuale:=$w
			r_ventilatori[azioneVentilatori]
			endpar
			
		choose $m in Umidita with true // Si imposta uno degli irrigatori
		do
			par
			umiditaAttuale:=$m
			r_irrigatori[azioneIrrigatori]
			endpar
		endpar
	
	endif
	
	
	endpar



// STATO INIZIALE
default init s0:
	// Luci spente
	function statoLuce($l in Luci) =  OFF
	// Irrigatori spenti
	function statoIrrigatore($i in Irrigatori) =  0
	// Ventilatori spenti
	function statoVentilatore($v in Ventilatori) =  SPENTO
	



