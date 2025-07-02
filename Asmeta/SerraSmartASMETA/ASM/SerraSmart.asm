// Nome asm
asm SerraSmart

// Importazione delle librerie necessarie (librerie standard ASMETA + logiche CTL e LTL per model checking)
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
static sogliaLuceMax : Integer

// ===============================
// FUNZIONI DERIVATE
// ===============================

// Controllo delle soglie della temperatura
derived temperaturaTroppoBassa : Boolean
derived temperaturaTroppoAlta : Boolean

// Controllo soglie umidità
derived umiditaTroppoBassa : Boolean
derived umiditaTroppoAlta : Boolean

// Controllo soglie luce
derived luceTroppoBassa : Boolean
derived luceTroppoAlta : Boolean

definitions:
// ===============================
// DEFINIZIONE FUNZIONI DERIVATE
// ===============================

// Controllo soglie temperatura
function temperaturaTroppoBassa = if(temperatura < sogliaTempMin) then true else false endif
function temperaturaTroppoAlta = if(temperatura > sogliaTempMax) then true else false endif


// Controllo soglie umidità
function umiditaTroppoBassa = if(umidita < sogliaUmiditaMin) then true else false endif
function umiditaTroppoAlta = if(umidita > sogliaUmiditaMax) then true else false endif

// Controllo soglie luce
function luceTroppoBassa = if(luce < sogliaLuceMin) then true else false endif
function luceTroppoAlta = if(luce > sogliaLuceMax) then true else false endif







