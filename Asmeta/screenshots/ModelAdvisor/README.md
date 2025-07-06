# Model Advisor - Serra Smart 🌱

Lo scopo del model advisor di ASMETA è quello di far eseguire ad ASMETA una verifica automatica del modello, per trovare:
- definizioni inutilizzate
- variabili mai modificate
- regole ridondanti o mai attivate
- incoerenze nella semantica ASM

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

Nel file `/Model_advisor.png/` si può visualizzare l'output del model advisor.



## Autore
Samuel Gherardi