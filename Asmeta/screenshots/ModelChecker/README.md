# Model Checker - Serra Smart 🌱

Il model checker di ASMETA è uno strumento automatico che verifica se il modello ASM soddisfa certe proprietà logiche, in tutti i possibili scenari e stati. I suoi scopi principali sono i seguenti
- verificare correttezza formale
- trovare errori logici
- dimostrare proprietà importanti come:
	- Safety: “non succede mai qualcosa di sbagliato”
	- Liveness: “prima o poi succede qualcosa di desiderato”
- eseguire test esaustivi su comportamenti non coperti dagli scenari

La sua esecuzione sul file `/SerraSmart.asm/` dà dei problemi relativi ai domini di tipo intero, i quali non sono supportati. Per questo motivo ho definito un modello semplificato contenente soltanto domini enumerativi e booleani,`/SerraSmartMinimal.asm/`, all'interno del quale si modellizza il funzionamento automatico o manuale della serra, con le seguenti modifiche:
- il dominio delle luci passa da intero a enumerativo
- il dominio degli irrigatori passa da intero a enumerativo
- il livello degli irrigatori passa da intero a enumerativo (MASSIMO, MEDIO, ZERO)
- le soglie massime e minime di luminosità, umidità e temperatura non vengono modellizzate
- il valore di luminosità attuale viene simulato come un enumerativo tra LALTA, LGIUSTA e LBASSA
- il valore di temperatura attuale viene simulato come un enumerativo tra TALTA, TGIUSTA e TBASSA
- il valore di umidità attuale viene simulato come un enumerativo tra UALTA, UGIUSTA e UBASSA
- le luci vengono accese se la luminosità attuale è LBASSA, oppure se la temperatura attuale è TBASSA
- i ventilatori vengono accesi se la temperatura attuale è TALTA
- gli irrigatori vengono accesi se l'umidità attuale è UBASSA
- le luci vengono spente se la luminosità attuale è LALTA
- i ventilatori vengono spenti se la temperatura attuale è TBASSA
- gli irrigatori vengono spenti se l'umidità attuale è UALTA


## Proprietà Definite
Ho definito le seguenti proprietà CTL
- Liveness: se la temperatura supera la soglia, prima o poi si attiva uno dei due ventilatori -->
  `CTLSPEC ag ((temperaturaAttuale = TALTA and sceltaModalita = AUTOMATICA) implies ef (statoVentilatore(PRINCIPALE) = ACCESO or statoVentilatore(SECONDARIO) = ACCESO ))`
- Safety: non devono essere accesi contemporaneamente tutti gli attuatori in qualsiasi momento -->
  `CTLSPEC not ag(
    (exist $l in Luci with statoLuce($l) = ON) and
    (exist $i in Irrigatori with statoIrrigatore($i) = MASSIMO) and
    (exist $v in Ventilatori with statoVentilatore($v) = ACCESO))`

e le seguenti proprietà LTL
- Until: le luci rimangono accese fino a quando la luce non supera la soglia -->
  `LTLSPEC g ((luminositaAttuale = LBASSA) implies u(statoLuce(LUCE1) = ON, luminositaAttuale = LBASSA))`
- Globale: se la serra è chiusa, nessun attuatore deve essere attivo -->
  `LTLSPEC g (
    serraChiusa implies
    (forall $l in Luci with statoLuce($l) = OFF) and
    (forall $i in Irrigatori with statoIrrigatore($i) = ZERO) and
    (forall $v in Ventilatori with statoVentilatore($v) = SPENTO)
    )`

Nei file `/CTL1.png/`,`/CTL2.png/`, `/LTL1.png/` e `/LTL2.png/`  si può visualizzare l'output del model checker durante il controllo delle diverse proprietà.



## Autore
Samuel Gherardi