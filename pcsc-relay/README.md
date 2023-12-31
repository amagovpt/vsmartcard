# PC/SC Relay

Welcome to PC/SC Relay. The purpose of PC/SC Relay is to relay a smart
card using an contact-less interface. Currently the following contact-less
**emulators** are supported:

- Hardware supported by [libnfc](http://www.libnfc.org/)
- OpenPICC
- [Android Smart Card
  Emulator](http://frankmorgner.github.io/vsmartcard/ACardEmulator/README.html)

Command APDUs are received with the contact-less interface and relayed. The
Response APDUs are then sent back via RFID. The contact-less data will be
relayed to one of the following **connectors**:

- to a *real* smart card inserted into one of the systems' smart card readers.
  The smart card reader must be accessible with PC/SC. The smart card may be
  contact-based *or* contact-less.
- to a [virtual smart
  card](http://frankmorgner.github.io/vsmartcard/ccid/README.html) that
  directly connects to `pcsc-relay`. The virtual smart card's native interface
  is used and (despite its name) PC/SC Relay does not need to access PC/SC in
  this case.

<!---
http://www.plantuml.com/plantuml/txt/SoWkIImgAStDuNBDBSr9BCalKj2rKr0gI2vErYrApKciL5AmKd3EpyrDp4jHS0nm2UL2bWEg1KhcvQKc0pLoGLcOHc3eWTjbfH2KMboGdrUS2Z7S8JKl1UWO0000

@startuml
skinparam responseMessageBelowArrow true
Emulator -> "pcsc-relay" : Command APDU
"pcsc-relay" -> Connector
Connector -> "pcsc-relay"
"pcsc-relay" -> Emulator : Response APDU
@enduml
-->
     ┌────────┐          ┌──────────┐          ┌─────────┐
     │Emulator│          │pcsc-relay│          │Connector│
     └───┬────┘          └────┬─────┘          └────┬────┘
         │    Command APDU    │                     │     
         │ ───────────────────>                     │     
         │                    │ ───────────────────>│     
         │                    │ <───────────────────│     
         │    Response APDU   │                     │     
         │ <───────────────────                     │     
     ┌───┴────┐          ┌────┴─────┐          ┌────┴────┐
     │Emulator│          │pcsc-relay│          │Connector│
     └────────┘          └──────────┘          └─────────┘
