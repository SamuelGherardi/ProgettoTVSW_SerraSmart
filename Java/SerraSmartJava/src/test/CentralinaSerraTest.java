package test;

import static org.junit.jupiter.api.Assertions.*;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import main.CentralinaSerra;
import main.Modalita;
import main.SerraSmartController;
import main.StatoLuce;
import main.StatoVentilatore;
import main.Ventilatore;

//Classe di test per la classe CentralinaSerra
class CentralinaSerraTest {
	
    private CentralinaSerra centralina;

    @BeforeEach
    public void setUp() {
        // Soglie: luceMin=200, luceMax=800, tempMin=15, tempMax=30, umiditaMin=30, umiditaMax=70
        SerraSmartController controller = new SerraSmartController(200, 800, 15, 30, 30, 70);
        controller.setSogliaLuceMin(200);
        controller.setSogliaLuceMax(800);
        controller.setSogliaTempMin(15);
        controller.setSogliaTempMax(30);
        controller.setSogliaUmiditaMin(30);
        controller.setSogliaUmiditaMax(70);
        centralina = new CentralinaSerra(3, 2, controller, Modalita.AUTOMATICA);
    }

    @Test
    public void testLuceInsufficienteAccendeLuci() {
        centralina.aggiornaSensori(25, 50, 100); // luce < sogliaLuceMin
        // Tutte le luci devono essere accese
        for (int i = 0; i < 3; i++) {
            assertEquals(StatoLuce.ON, centralina.getStatoLuce(i));
        }
        assertEquals(Modalita.AUTOMATICA, centralina.getModalita());
    }

    @Test
    public void testLuceTroppoAltaSpegneLuci() {
        centralina.accendiLuci(); // Prima accendiamo
        centralina.aggiornaSensori(25, 50, 900); // luce > sogliaLuceMax
        for (int i = 0; i < 3; i++) {
            assertEquals(StatoLuce.OFF, centralina.getStatoLuce(i));
        }
    }

    @Test
    public void testTemperaturaTroppoAltaAccendeVentilatori() {
        centralina.aggiornaSensori(40, 50, 300); // temperatura > sogliaTempMax
        assertEquals(StatoVentilatore.ACCESO, centralina.getStatoVentilatore(Ventilatore.PRINCIPALE));
        assertEquals(StatoVentilatore.ACCESO, centralina.getStatoVentilatore(Ventilatore.SECONDARIO));
    }

    @Test
    public void testTemperaturaTroppoBassaSpegneVentilatori() {
        centralina.accendiVentilatori();
        centralina.aggiornaSensori(10, 50, 300); // temperatura < sogliaTempMin
        assertEquals(StatoVentilatore.SPENTO, centralina.getStatoVentilatore(Ventilatore.PRINCIPALE));
        // Tutte le luci devono essere accese
        for (int i = 0; i < 3; i++) {
            assertEquals(StatoLuce.ON, centralina.getStatoLuce(i));
        }
    }

    @Test
    public void testUmiditaTroppoAltaSpegneIrrigatori() {
        centralina.accendiIrrigatori();
        centralina.aggiornaSensori(25, 90, 300); // umidità  > sogliaUmiditaMax
        for (int i = 0; i < 2; i++) {
            assertEquals(0, centralina.getLivelloIrrigatore(i));
        }
    }
    
    @Test
    public void testUmiditaTroppoBassaAccendeIrrigatori() {
        centralina.spegniIrrigatori();
        centralina.aggiornaSensori(25, 20, 300); // umidità  < sogliaUmiditaMin
        for (int i = 0; i < 2; i++) {
            assertEquals(100, centralina.getLivelloIrrigatore(i));
        }
    }

    @Test
    public void testManualeModificaStato() {
        centralina.setModalita(Modalita.MANUALE);
        centralina.aggiornaSensori(25, 20, 300);
        centralina.setLuce(0, StatoLuce.ON);
        centralina.setVentilatore(Ventilatore.PRINCIPALE, StatoVentilatore.ACCESO);
        centralina.setIrrigatore(0, 52);
        assertEquals(Modalita.MANUALE, centralina.getModalita());
        assertEquals(StatoLuce.ON, centralina.getStatoLuce(0));
        assertEquals(StatoVentilatore.ACCESO, centralina.getStatoVentilatore(Ventilatore.PRINCIPALE));
        assertEquals(52, centralina.getLivelloIrrigatore(0));
        
    }
    
    @Test
    public void testModificheErrate() {
    	centralina.spegniLuci();
    	centralina.spegniVentilatori();
    	centralina.spegniIrrigatori();
    	
    	//SetLuce
    	centralina.setModalita(Modalita.AUTOMATICA);
    	centralina.setLuce(0, StatoLuce.OFF);
    	centralina.setModalita(Modalita.MANUALE);
    	centralina.setLuce(-1, StatoLuce.OFF);
    	
    	//SetVentilatore
    	centralina.setModalita(Modalita.AUTOMATICA);
    	centralina.setVentilatore(Ventilatore.SECONDARIO, StatoVentilatore.ACCESO);
    	
    	//SetIrrigatore
    	centralina.setModalita(Modalita.AUTOMATICA);
    	centralina.setIrrigatore(-1, 50);
    	centralina.setModalita(Modalita.MANUALE);
    	centralina.setIrrigatore(-1, 50);
    	
    	//getStatoLuce
    	assertNull(centralina.getStatoLuce(-1));
    	
    	//getLivelloIrrigatore
    	assertEquals(-1,centralina.getLivelloIrrigatore(-1));
    	
    }
    
    @Test
    public void testMCDC() {
    	centralina.spegniLuci();
    	centralina.spegniVentilatori();
    	centralina.spegniIrrigatori();
    	centralina.setModalita(Modalita.MANUALE);
    	//setLuce
    	//if(l>=0 && l<luci.length)
    	centralina.setLuce(0, StatoLuce.OFF);
    	centralina.setLuce(-1, StatoLuce.OFF);
    	centralina.setLuce(5, StatoLuce.OFF);
    	centralina.setModalita(Modalita.AUTOMATICA);
    	centralina.setLuce(0, StatoLuce.OFF);
    	//setVentilatore
    	centralina.setModalita(Modalita.MANUALE);
    	centralina.setVentilatore(Ventilatore.PRINCIPALE, StatoVentilatore.SPENTO);
    	centralina.setModalita(Modalita.AUTOMATICA);
    	centralina.setVentilatore(Ventilatore.PRINCIPALE, StatoVentilatore.SPENTO);
    	//setIrrigatore
    	//if(i>=0 && i<irrigatori.length && livello>=0 && livello<=100)
    	centralina.setModalita(Modalita.MANUALE);
    	centralina.setIrrigatore(0, 50);
    	centralina.setIrrigatore(-1, 50);
    	centralina.setIrrigatore(5, 50);
    	centralina.setIrrigatore(0, -1);
    	centralina.setIrrigatore(0, 200);
    	centralina.setModalita(Modalita.AUTOMATICA);
    	centralina.setIrrigatore(0, 50);
    	//getStatoLuce
    	//if(l>=0 && l<luci.length)
    	centralina.setModalita(Modalita.MANUALE);
    	centralina.getStatoLuce(0);
    	centralina.getStatoLuce(-1);
    	centralina.getStatoLuce(5);
    	centralina.setModalita(Modalita.AUTOMATICA);
    	centralina.getStatoLuce(0);
    	//getLivelloirrigatori
    	//if(i>=0 && i<irrigatori.length)
    	centralina.setModalita(Modalita.MANUALE);
    	centralina.getLivelloIrrigatore(0);
    	centralina.getLivelloIrrigatore(-1);
    	centralina.getLivelloIrrigatore(5);
    	centralina.setModalita(Modalita.AUTOMATICA);
    	centralina.getLivelloIrrigatore(0);
    	//setVentilatore
    	centralina.setModalita(Modalita.MANUALE);
    	centralina.setVentilatore(Ventilatore.PRINCIPALE, StatoVentilatore.SPENTO);
    	centralina.setModalita(Modalita.AUTOMATICA);
    	centralina.setVentilatore(Ventilatore.PRINCIPALE, StatoVentilatore.SPENTO);
    	//aggiornaSensori
    	centralina.setModalita(Modalita.AUTOMATICA);
    	centralina.aggiornaSensori(0, 0, 0);
    	centralina.aggiornaSensori(50, 90, 900);
    	centralina.setModalita(Modalita.MANUALE);
    	centralina.aggiornaSensori(0, 0, 0);
    	
    }

}
