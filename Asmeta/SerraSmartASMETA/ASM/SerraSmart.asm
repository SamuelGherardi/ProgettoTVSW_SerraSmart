//Nome asm
asm SerraSmart

//Importazione delle librerie necessarie (librerie standard ASMETA + logiche CTL e LTL per model checking)
import ../STDL/StandardLibrary
import ../STDL/CTLLibrary
import ../STDL/LTLLibrary

signature:

// ===============================
// DEFINIZIONE DEI DOMINI
// ===============================
// Domini enumerativi
enum domain StatoAttuatore = {ON | OFF}
enum domain ModalitaControllo = {AUTOMATICO | MANUALE}

// Tipi di attuatori
enum domain Attuatore = {VENTOLA | IRRIGAZIONE | LUCE}

// ==============================
// Domini astratti
abstract domain Utente

// ===============================
// FUNZIONI MONITORATE (input esterni)
// ===============================
monitored temperatura : Integer
monitored umidita : Integer
monitored luce : Integer
monitored modalita : ModalitaControllo

// ===============================
// FUNZIONI CONTROLLATE (attuatori)
// ===============================
controlled statoAttuatore : Attuatore -> StatoAttuatore

// ===============================
// FUNZIONI STATICHE (soglie configurabili)
// ===============================
static sogliaTempMin : Integer
static sogliaTempMax : Integer
static sogliaUmiditaMin : Integer
static sogliaUmiditaMax : Integer
static sogliaLuceMin : Integer

// ===============================
// FUNZIONI DERIVATE
// ===============================
derived temperaturaTroppoAlta : Boolean












