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
	
	// Regola che va ad accendere tutte le luci nel momento in cui la luminosità segnalata è minore della soglia minima
	rule r_luciAccese($azione in AzioniLuci) = 
		forall $l in Luci with statoLuce($l) = OFF
		do
			statoLuce($l) := ON
			
							

	
	// REGOLA PRINCIPALE
	main rule r_Main =
	par	// Si simula in modo casuale il livello di luminosità presente nella serra
		choose $x in Luminosita with true
		do 	if ($x < sogliaLuceMin)
			then r_luciAccese[azioneLuci]
			endif
		
		// Se la temperatura risulta sotto la soglia minima si vanno ad accedendere tutte le luci
		choose $t in Temperatura with true
		do 	if ($t < sogliaTempMin)
			then r_luciAccese[azioneLuci]
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
	



