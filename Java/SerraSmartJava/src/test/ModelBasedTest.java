package test;

import static org.junit.jupiter.api.Assertions.*;

import org.junit.jupiter.api.Test;

import main.CentralinaSerra;
import main.Modalita;
import main.SerraSmartController;
import main.StatoLuce;
import main.StatoVentilatore;
import main.Ventilatore;

//classe di test tradotto da scenario Avalla di Asmeta (Scenario1.avalla)
//in questo scenario si valuta il corretto funzionamento della gestione automatica della serra
class ModelBasedTest {

	@Test
	public void AvallaTest() {
		// Soglie: luceMin=10, luceMax=50, tempMin=5, tempMax=30, umiditaMin=10, umiditaMax=50
        SerraSmartController controller = new SerraSmartController(10, 50, 5, 30, 10, 50);
        CentralinaSerra centralina = new CentralinaSerra(5, 3, controller, Modalita.AUTOMATICA);
        
        //Controllo che inizialmente tutti gli attuatori siano spenti
        for (int i = 0; i < 5; i++) {
            assertEquals(StatoLuce.OFF, centralina.getStatoLuce(i));
        }
        assertEquals(StatoVentilatore.SPENTO, centralina.getStatoVentilatore(Ventilatore.PRINCIPALE));
        assertEquals(StatoVentilatore.SPENTO, centralina.getStatoVentilatore(Ventilatore.SECONDARIO));
        for (int i = 0; i < 3; i++) {
            assertEquals(0, centralina.getLivelloIrrigatore(i));
        }
        
        //setto la modalità in automatico
        centralina.setModalita(Modalita.AUTOMATICA);
        
        //Forzo i valori rilevati sulla luminosità, sulla temperatura e sull'umidità
        //luminosità  ==> mi aspetto che si accendano tutte le luci
        //temperatura ==> mi aspetto che si accendano entrambi i ventilatori
        //umidità ==> mi aspetti che si attivino al massimo tutti gli irrigatori
        centralina.aggiornaSensori(40, 9, 8);
        
        //Controllo che effettivamente tutti gli attuatori si siano attivati
        for (int i = 0; i < 5; i++) {
            assertEquals(StatoLuce.ON, centralina.getStatoLuce(i));
        }
        assertEquals(StatoVentilatore.ACCESO, centralina.getStatoVentilatore(Ventilatore.PRINCIPALE));
        assertEquals(StatoVentilatore.ACCESO, centralina.getStatoVentilatore(Ventilatore.SECONDARIO));
        for (int i = 0; i < 3; i++) {
            assertEquals(100, centralina.getLivelloIrrigatore(i));
        }
        
        //Forzo i valori rilevati sulla luminosità, sulla temperatura e sull'umidità
        //luminosità  ==> mi aspetto che si spengano tutte le luci
        //temperatura ==> mi aspetto che i ventilatori restino accesi
        //umidità ==> mi aspetti che si spengano tutti gli irrigatori
        centralina.aggiornaSensori(40, 65, 60);
        
        //Controllo che effettivamente tutti gli attuatori cambino stato nel modo corretto
        for (int i = 0; i < 5; i++) {
            assertEquals(StatoLuce.OFF, centralina.getStatoLuce(i));
        }
        assertEquals(StatoVentilatore.ACCESO, centralina.getStatoVentilatore(Ventilatore.PRINCIPALE));
        assertEquals(StatoVentilatore.ACCESO, centralina.getStatoVentilatore(Ventilatore.SECONDARIO));
        for (int i = 0; i < 3; i++) {
            assertEquals(0, centralina.getLivelloIrrigatore(i));
        }
        
        //Forzo i valori rilevati sulla luminosità, sulla temperatura e sull'umidità
        //luminosità  ==> mi aspetto che le luci restino spente
        //temperatura ==> mi aspetto che i ventilatori si spengano, e che le luci si accendano
        //umidità ==> mi aspetti che tutti gli irrigatori restino spenti
        centralina.aggiornaSensori(3, 65, 60);
        
      //Controllo che effettivamente tutti gli attuatori cambino stato nel modo corretto
        for (int i = 0; i < 5; i++) {
            assertEquals(StatoLuce.ON, centralina.getStatoLuce(i));
        }
        assertEquals(StatoVentilatore.SPENTO, centralina.getStatoVentilatore(Ventilatore.PRINCIPALE));
        assertEquals(StatoVentilatore.SPENTO, centralina.getStatoVentilatore(Ventilatore.SECONDARIO));
        for (int i = 0; i < 3; i++) {
            assertEquals(0, centralina.getLivelloIrrigatore(i));
        }
	}

}
