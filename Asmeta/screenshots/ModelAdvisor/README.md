# Model Advisor - Serra Smart 🌱

Lo scopo del model advisor di ASMETA è quello di far eseguire ad ASMETA una verifica automatica del modello, per trovare:
- definizioni inutilizzate
- variabili mai modificate
- regole ridondanti o mai attivate
- incoerenze nella semantica ASM

La sua esecuzione sul file `/SerraSmart.asm/` dà dei problemi relativi ai domini di tipo intero, i quali non sono supportati. Per questo motivo ho definito un modello semplificato contenente soltanto domini enumerativi e booleani,`/SerraSmartMinimal.asm/`, all'interno del quale si modellizza soltanto il funzionamento di 2 luci che possono essere accese oppure spente.
Nel file `/Model_advisor.png/` si può visualizzare l'output del model advisor.



## Autore
Samuel Gherardi