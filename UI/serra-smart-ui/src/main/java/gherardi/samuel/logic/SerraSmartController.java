package gherardi.samuel.logic;
//Questa classe conterrà la logica centrale per gestire gli attuatori in base ai valori ambientali
public class SerraSmartController {
	
	private /*@ spec_public */ int sogliaLuceMin;
	private /*@ spec_public */ int sogliaLuceMax;
    private /*@ spec_public */ int sogliaTempMin;
    private /*@ spec_public */ int sogliaTempMax;
    private /*@ spec_public */ int sogliaUmiditaMin;
    private /*@ spec_public */ int sogliaUmiditaMax;
    
    //Definizione invarianti
    //1- Le soglie di luminosità massima e minima devono essere sempre >=0 e <=1000 (espressi in lux)
    //2- Le soglie di temperatura massima e minima devono essere sempre >=0 e <=100 (espressi in gradi centigradi)
    //3- Le soglie di umidità massima e minima devono essere sempre >=0 e <=100 (espressi in %)
    //4- La soglia minima deve essere sempre minore o uguale rispetto alla soglia massima
    //@ public invariant sogliaLuceMin>=0 && sogliaLuceMin<=1000;
    //@ public invariant sogliaLuceMax>=0 && sogliaLuceMax<=1000;
    //@ public invariant sogliaTempMin>=0 && sogliaTempMin<=100;
    //@ public invariant sogliaTempMax>=0 && sogliaTempMax<=100;
    //@ public invariant sogliaUmiditaMin>=0 && sogliaUmiditaMin<=100;
    //@ public invariant sogliaUmiditaMax>=0 && sogliaUmiditaMax<=100;
    //@ public invariant sogliaLuceMin<=sogliaLuceMax;
    //@ public invariant sogliaTempMin<=sogliaTempMax;
    //@ public invariant sogliaUmiditaMin<=sogliaUmiditaMax;
    
    //Costruttore
    //@ requires luceMin>=0 && luceMin<=1000 && luceMin<=luceMax;
    //@ requires luceMax>=0 && luceMax<=1000 && luceMax>=luceMin;
    //@ requires tempMin>=0 && tempMin<=100 && tempMin<=tempMax;
    //@ requires tempMax>=0 && tempMax<=100 && tempMax>=tempMin;
    //@ requires uMin>=0 && uMin<=100 && uMin<=uMax;
    //@ requires uMax>=0 && uMax<=100 && uMax>=uMin;
    //@ ensures sogliaLuceMin==luceMin;
    //@ ensures sogliaLuceMax==luceMax;
    //@ ensures sogliaTempMin==tempMin;
    //@ ensures sogliaTempMax==tempMax;
    //@ ensures sogliaUmiditaMin==uMin;
    //@ ensures sogliaUmiditaMax==uMax;
    public SerraSmartController(int luceMin, int luceMax, int tempMin, int tempMax, int uMin, int uMax) {
    	sogliaLuceMin=luceMin;
    	sogliaLuceMax=luceMax;
    	
    	sogliaTempMin=tempMin;
    	sogliaTempMax=tempMax;
    	
    	sogliaUmiditaMin=uMin;
    	sogliaUmiditaMax=uMax;
    	
    }
    
    //Metodo che specifica se la luminosità è insufficiente
    //Pre-condizioni:
    //1- La luminosità rilevata deve essere tra gli 0 e i 1000 lux
    //Post-condizioni:
    //1- il metodo deve restituire true se la luminosità è insufficiente, altrimenti false
    //@ requires lux >= 0 && lux <= 1000;
    //@ ensures \result <==> (lux < sogliaLuceMin);
    public /*@ pure @*/ boolean luceInsufficiente(int lux) {
        return lux < sogliaLuceMin;
    }
    
    //Metodo che specifica se la luminosità è troppo elevata
    //Pre-condizioni:
    //1- La luminosità rilevata deve essere tra gli 0 e i 1000 lux
    //Post-condizioni:
    //1- il metodo deve restituire true se la luminosità è troppo alta, altrimenti false
    //@ requires lux >= 0 && lux <= 1000;
    //@ ensures \result <==> (lux > sogliaLuceMax);
    public /*@ pure @*/ boolean luceTroppoAlta(int lux) {
        return lux > sogliaLuceMax;
    }
    
    //Metodo che specifica se la temperatura rilevata è troppo bassa
    //Pre-condizioni:
    //1- La temperatura rilevata deve essere al massimo 100 gradi centigradi
    //Post-condizioni:
    //1- il metodo deve restituire true se la temperatura è insufficiente, altrimenti false
    //@ requires temperatura <= 100;
    //@ ensures \result <==> (temperatura < sogliaTempMin);
    public /*@ pure @*/ boolean temperaturaTroppoBassa(int temperatura) {
        return temperatura < sogliaTempMin;
    }
    
    //Metodo che specifica se la temperatura rilevata è troppo alta
    //Pre-condizioni:
    //1- La temperatura rilevata deve essere al massimo 100 gradi centigradi
    //Post-condizioni:
    //1- il metodo deve restituire true se la temperatura è troppo elevata, altrimenti false
    //@ requires temperatura <= 100;
    //@ ensures \result <==> (temperatura > sogliaTempMax);
    public /*@ pure @*/ boolean temperaturaTroppoAlta(int temperatura) {
        return temperatura > sogliaTempMax;
    }

    
    //Metodo che specifica se l'umidità rilevata è troppo bassa
    //Pre-condizioni:
    //1- L'umidità rilevata deve essere compresa tra lo 0% e il 100%
    //Post-condizioni:
    //1- il metodo deve restituire true se l'umidità è insufficiente, altrimenti false
    //@ requires umidita >= 0 && umidita <= 100;
    //@ ensures \result <==> (umidita < sogliaUmiditaMin);
    public /*@ pure @*/ boolean umiditaTroppoBassa(int umidita) {
        return umidita < sogliaUmiditaMin;
    }
    
    //Metodo che specifica se l'umidità rilevata è troppo alta
    //Pre-condizioni:
    //1- L'umidità rilevata deve essere compresa tra lo 0% e il 100%
    //Post-condizioni:
    //1- il metodo deve restituire true se l'umidità è troppo alta, altrimenti false
    //@ requires umidita >= 0 && umidita <= 100;
    //@ ensures \result <==> (umidita > sogliaUmiditaMax);
    public /*@ pure @*/ boolean umiditaTroppoAlta(int umidita) {
        return umidita > sogliaUmiditaMax;
    }
    
    //Metodo per settare la luminosità minima
    //@ requires l >= 0 && l <= 1000 && l<=sogliaLuceMax;
    //@ ensures sogliaLuceMin == l;
    public void setSogliaLuceMin(int l) {
        sogliaLuceMin = l;
    }
    
    //Metodo per settare la luminosità massima
    //@ requires l >= 0 && l <= 1000 && l>=sogliaLuceMin;
    //@ ensures sogliaLuceMax == l;
    public void setSogliaLuceMax(int l) {
        sogliaLuceMax = l;
    }
    
    //Metodo per settare la temperatura minima
    //@ requires t >= 0 && t <= 100 && t<=sogliaTempMax;
    //@ ensures sogliaTempMin == t;
    public void setSogliaTempMin(int t) {
        sogliaTempMin = t;
    }
    
    //Metodo per settare la temperatura massima
    //@ requires t >= 0 && t <= 100 && t>=sogliaTempMin;
    //@ ensures sogliaTempMax == t;
    public void setSogliaTempMax(int t) {
        sogliaTempMax = t;
    }

    //Metodo per settare l'umidità minima
    //@ requires u >= 0 && u <= 100 && u<=sogliaUmiditaMax;
    //@ ensures sogliaUmiditaMin == u;
    public void setSogliaUmiditaMin(int u) {
        sogliaUmiditaMin = u;
    }
    
    //Metodo per settare l'umidità massima
    //@ requires u >= 0 && u <= 100 && u>=sogliaUmiditaMin;
    //@ ensures sogliaUmiditaMax == u;
    public void setSogliaUmiditaMax(int u) {
        sogliaUmiditaMax = u;
    }
    
    public int getSogliaLuceMin() {
        return sogliaLuceMin;
    }
    

    public int getSogliaLuceMax() {
        return sogliaLuceMax;
    }
    

    public int getSogliaTempMin() {
        return sogliaTempMin;
    }
    

    public int getSogliaTempMax() {
        return sogliaTempMax;
    }


    public int getSogliaUmiditaMin() {
        return sogliaUmiditaMin;
    }
    

    public int getSogliaUmiditaMax() {
        return sogliaUmiditaMax;
    } 
    
}
