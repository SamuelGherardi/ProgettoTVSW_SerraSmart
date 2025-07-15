package test;

import static org.junit.jupiter.api.Assertions.*;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;

import main.CentralinaSerra;
import main.Modalita;
import main.SerraSmartController;
import main.StatoLuce;
import main.StatoVentilatore;
import main.Ventilatore;

//Classe di test per effettuare il testing combinatoriale pairwise tramite algoritmo IPO
class CombinatorialTest {

	@ParameterizedTest
	@CsvSource({
	    "5,2,5",
	    "5,20,40",
	    "5,40,90",
	    "30,20,90",
	    "30,40,5",
	    "30,2,40",
	    "80,40,40",
	    "80,2,90",
	    "80,20,5"
	})
	public void CombinatorialTesting(int lux, int temp, int umid) {
		SerraSmartController controller = new SerraSmartController(10, 50, 5, 30, 10, 50);
	    CentralinaSerra centralina = new CentralinaSerra(5, 3, controller, Modalita.AUTOMATICA);
	    centralina.aggiornaSensori(temp, umid, lux);

	    System.out.printf("Test con lux=%d, temp=%d, umid=%d%n", lux, temp, umid);
	    // Per ogni combinazione stampo lo stato degli attuatori
	    for (int i = 0; i < 5; i++) {
	        System.out.println("Luce " + i + ": " + centralina.getStatoLuce(i));
	        
	    }
	    for (Ventilatore v : Ventilatore.values()) {
	        System.out.println("Ventilatore " + v + ": " + centralina.getStatoVentilatore(v));
	    }
	    for (int i = 0; i < 3; i++) {
	        System.out.println("Irrigatore " + i + ": " + centralina.getLivelloIrrigatore(i) + "%");
	    }
	    System.out.println("------");
	    
	    //test con lux=5, temp=2, umid=5
	    // Attese: luci ON, vent ON, irrigatori 100%
	    if (lux == 5) {
	        for (int i = 0; i < 5; i++) assertEquals(StatoLuce.ON, centralina.getStatoLuce(i));
	    } else if (lux == 80 && temp ==40) {
	        for (int i = 0; i < 5; i++) assertEquals(StatoLuce.OFF, centralina.getStatoLuce(i));
	    }

	    if (temp == 40) {
	        for (Ventilatore v : Ventilatore.values()) assertEquals(StatoVentilatore.ACCESO, centralina.getStatoVentilatore(v));
	    } else if (temp == 20) {
	        for (Ventilatore v : Ventilatore.values()) assertEquals(StatoVentilatore.SPENTO, centralina.getStatoVentilatore(v));
	    }

	    if (umid == 5) {
	        for (int i = 0; i < 3; i++) assertEquals(100, centralina.getLivelloIrrigatore(i));
	    } else if (umid == 90) {
	        for (int i = 0; i < 3; i++) assertEquals(0, centralina.getLivelloIrrigatore(i));
	    }
	    
	}

}
