package gherardi.samuel.base.ui.view;

import gherardi.samuel.base.ui.component.ViewToolbar;

import com.vaadin.flow.component.UI;
import com.vaadin.flow.component.button.Button;
import com.vaadin.flow.component.html.NativeLabel;
import com.vaadin.flow.component.html.Div;
import com.vaadin.flow.component.html.H2;
import com.vaadin.flow.component.html.Main;
import com.vaadin.flow.component.orderedlayout.VerticalLayout;
import com.vaadin.flow.router.Route;
import com.vaadin.flow.theme.lumo.LumoUtility;
import jakarta.annotation.security.PermitAll;
import gherardi.samuel.logic.*;
/**
 * This view shows up when a user navigates to the root ('/') of the application.
 */
@Route
@PermitAll // When security is enabled, allow all authenticated users
public final class MainView extends VerticalLayout {

    private final CentralinaSerra centralina;

    private final NativeLabel titolo = new NativeLabel("Dashboard Serra Smart");
    private final NativeLabel statoModalita = new NativeLabel();
    private final NativeLabel statoLuci = new NativeLabel();
    private final NativeLabel statoVentilatori = new NativeLabel();

    public MainView() {
        setPadding(true);
        setSpacing(true);
        setDefaultHorizontalComponentAlignment(Alignment.START);

        // 🔧 Istanzia controller e centralina
        SerraSmartController controller = new SerraSmartController(200, 800, 15, 30, 30, 70);
        centralina = new CentralinaSerra(3, 2, controller, Modalita.AUTOMATICA);

        // 🟢 Pulsante: cambia modalità
        Button toggleModalita = new Button("Cambia modalità");
        toggleModalita.addClickListener(e -> {
            if (centralina.getModalita() == Modalita.AUTOMATICA) {
                centralina.setModalita(Modalita.MANUALE);
            } else {
                centralina.setModalita(Modalita.AUTOMATICA);
            }
            aggiornaStatoUI();
        });

        // 🔄 Pulsante: simula nuovi dati sensore
        Button simula = new Button("Simula dati (temp=32, lux=150, umid=20)");
        simula.addClickListener(e -> {
            centralina.aggiornaSensori(32, 20, 150); // valori casuali
            aggiornaStatoUI();
        });

        // 🧾 Layout e contenuti
        //add(new H2("Serra Smart"), statoModalita, statoLuci, statoVentilatori, toggleModalita, simula);
        H2 header = new H2("Serra Smart");

        add(header);
        add(statoModalita);
        add(statoLuci);
        add(statoVentilatori);
        add(toggleModalita);
        add(simula);

        aggiornaStatoUI();
    }

    private void aggiornaStatoUI() {
        statoModalita.setText("Modalità attuale: " + centralina.getModalita());

        StringBuilder luci = new StringBuilder("Luci: ");
        for (int i = 0; i < 3; i++) {
            luci.append("L").append(i).append("=").append(centralina.getStatoLuce(i)).append(" ");
        }
        statoLuci.setText(luci.toString());

        StringBuilder vent = new StringBuilder("Ventilatori: ");
        for (Ventilatore v : Ventilatore.values()) {
            vent.append(v.name()).append("=").append(centralina.getStatoVentilatore(v)).append(" ");
        }
        statoVentilatori.setText(vent.toString());
    }
	
	
}
