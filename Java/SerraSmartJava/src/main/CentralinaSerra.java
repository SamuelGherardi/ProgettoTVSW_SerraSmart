package main;

import java.util.HashMap;

//Classe che gestisce gli attuatori, la logica e l'interfaccia con il controller
public class CentralinaSerra {
	
	private StatoLuce[] luci;
	private HashMap<Ventilatore, StatoVentilatore> ventilatori;
	private int[] irrigatori;
	
	private Modalita modalita;
	private SerraSmartController controller;
	
	//Costruttore
	public CentralinaSerra(int n_luci, int n_irrigatori, SerraSmartController controller, Modalita modalita) {
		
		this.luci = new StatoLuce[n_luci];
		for(int i=0; i<n_luci;i++) {
			luci[i]=StatoLuce.OFF; //Inizialmente tutte le luci all'interno della serra sono spente
		}
		
		this.irrigatori = new int[n_irrigatori];
		for(int i=0; i<n_irrigatori; i++) {
			irrigatori[i]=0; //Inizialmente tutti gli irrigatori sono spenti
		}
		
		this.ventilatori = new HashMap<Ventilatore, StatoVentilatore>();
		this.ventilatori.put(Ventilatore.PRINCIPALE, StatoVentilatore.SPENTO); //Inizialmente entrambi i ventilatori sono spenti
		this.ventilatori.put(Ventilatore.SECONDARIO, StatoVentilatore.SPENTO);
		
		this.modalita=modalita;
		this.controller=controller;
	}
	
	//Metodo che permette di definire la modalità di gestione della serra
	public void setModalita(Modalita m) {
        this.modalita = m;
    }
	
    public Modalita getModalita() {
        return modalita;
    }
    
    //Metodo che va ad accendere tutte le luci della serra
    public void accendiLuci() {
    	for(int i=0; i<luci.length;i++) {
			luci[i]=StatoLuce.ON;
		}
    }
    
    //Metodo che va a spegnere tutte le luci della serra
    public void spegniLuci() {
    	for(int i=0; i<luci.length;i++) {
			luci[i]=StatoLuce.OFF; 
		}
    }
    
    //Metodo che va ad accendere tutti i ventilatori della serra
    public void accendiVentilatori() {
    	ventilatori.replace(Ventilatore.PRINCIPALE, StatoVentilatore.SPENTO, StatoVentilatore.ACCESO);
    	ventilatori.replace(Ventilatore.SECONDARIO, StatoVentilatore.SPENTO, StatoVentilatore.ACCESO);
    }
    
    //Metodo che va a spegnere tutti i ventilatori della serra
    public void spegniVentilatori() {
    	ventilatori.replace(Ventilatore.PRINCIPALE, StatoVentilatore.ACCESO, StatoVentilatore.SPENTO);
    	ventilatori.replace(Ventilatore.SECONDARIO, StatoVentilatore.ACCESO, StatoVentilatore.SPENTO);
    }
    
    //Metodo che va ad accendere al massimo tutti gli irrigatori della serra
    public void accendiIrrigatori() {
    	for(int i=0; i<irrigatori.length;i++) {
			irrigatori[i]=100;
		}
    }
    
    //Metodo che va a spegnere tutti gli irrigatori della serra
    public void spegniIrrigatori() {
    	for(int i=0; i<irrigatori.length;i++) {
			irrigatori[i]=0;
		}
    }
    
    //Metodo che va ad aggiornare i valori di temperatura, umidità e luminosità all'interno della serra 
    public void aggiornaSensori(int temperatura, int umidita, int lux) {
    	
    	if (modalita == Modalita.AUTOMATICA) {
    		//Se la luce è insufficiente si accendono tutte le luci
            if(controller.luceInsufficiente(lux)) {
            	accendiLuci();
            }
            //Se la luce è troppo alta si spengono tutte le luci
            if(controller.luceTroppoAlta(lux)) {
            	spegniLuci();
            }
            //Se la temperatura è troppo bassa allora si spengono tutti i ventilatori e si accendono tutte le luci
            if(controller.temperaturaTroppoBassa(temperatura)) {
            	spegniVentilatori();
            	accendiLuci();
            }
            //Se la temperatura è troppo alta allora si accendono tutti i ventilatori della serra
            if(controller.temperaturaTroppoAlta(temperatura)) {
            	accendiVentilatori();
            }
            //Se l'umidità è troppo bassa si accendono al massimo tutti gli irrigatori
            if(controller.umiditaTroppoBassa(umidita)) {
            	accendiIrrigatori();
            }
            //Se l'umidità è troppo alta si spengono tutti gli irrigatori
            if(controller.umiditaTroppoAlta(umidita)) {
            	spegniIrrigatori();
            }
            
        }

    }
    
    //Metodo che permette di accendere oppure spegnere una luce manualmente
    public void setLuce(int l, StatoLuce s) {
    	
    	if(modalita==Modalita.MANUALE) {
    		if(l>=0 && l<luci.length) {
    			luci[l]=s;
    		}
    	}
    	
    }
    
    //Metodo che permette di accendere oppure spegnere un ventilatore manualmente
    public void setVentilatore(Ventilatore v, StatoVentilatore s) {
    	
    	if(modalita==Modalita.MANUALE) {
    		ventilatori.replace(v, s);
    	}
    	
    }
    
    
    //Metodo che permette di settare il livello di apertura di un particolare irrigatore all'interno della serra
    public void setIrrigatore(int i, int livello) {
    	
    	if(modalita==Modalita.MANUALE) {
    		if(i>=0 && i<irrigatori.length && livello>=0 && livello<=100) {
    			irrigatori[i]=livello;
    		}
    	}
    	
    }
    
    //Metodo che restituisce lo stato di una particolare luce all'interno della serra
    public StatoLuce getStatoLuce(int l) {
    	
    	StatoLuce sl=null;
    	
    	if(l>=0 && l<luci.length) {
    		sl=luci[l];
    	}
    	
    	return sl;
    }
    
    //Metodo che restituisce lo stato di un particolare ventilatore all'interno della serra
    public StatoVentilatore getStatoVentilatore(Ventilatore v) {
    	return ventilatori.get(v);
    }
    
    //Metodo che restituisce il livello di un particolare irrigatore all'interno della serra
    public int getLivelloIrrigatore(int i) {
    	
    	int si=-1; //se il numero dell'irrigatore non è presente, viene restituito un valore negativo
    	
    	if(i>=0 && i<irrigatori.length) {
    		si=irrigatori[i];
    	}
    	
    	return si;
    }
	
}
