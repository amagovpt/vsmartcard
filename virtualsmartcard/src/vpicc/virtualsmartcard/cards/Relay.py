#
# Copyright (C) 2015 Frank Morgner
#
# This file is part of virtualsmartcard.
#
# virtualsmartcard is free software: you can redistribute it and/or modify it
# under the terms of the GNU General Public License as published by the Free
# Software Foundation, either version 3 of the License, or (at your option) any
# later version.
#
# virtualsmartcard is distributed in the hope that it will be useful, but
# WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
# FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
# more details.
#
# You should have received a copy of the GNU General Public License along with
# virtualsmartcard.  If not, see <http://www.gnu.org/licenses/>.
#

import atexit
import logging
import smartcard
import sys
from virtualsmartcard.VirtualSmartcard import SmartcardOS
from virtualsmartcard.cards.RelayMiddleman import RelayMiddleman


class RelayOS(SmartcardOS):
    """
    This class implements relaying of a (physical) smartcard. The RelayOS
    forwards the command APDUs received from the vpcd to the real smartcard via
    an actual smart card reader and sends the responses back to the vpcd.
    This class can be used to implement relay or MitM attacks.
    """
    def __init__(self, readernum, mitm=RelayMiddleman()):
        """
        Initialize the connection to the (physical) smart card via a given
        reader
        """

        # See which readers are available
        readers = smartcard.System.listReaders()
        if len(readers) <= readernum:
            logging.critical("Invalid number of reader '%u' (only %u available)",
                          readernum, len(readers))
            sys.exit()

        # Connect to the reader and its card
        # XXX this is a workaround, see on sourceforge bug #3083254
        # should better use
        # self.reader = smartcard.System.readers()[readernum]
        self.reader = readers[readernum]
        try:
            self.session = smartcard.Session(self.reader)
        except smartcard.Exceptions.CardConnectionException as e:
            logging.critical("Error connecting to card: %s", str(e))
            sys.exit()

        logging.info("Connected to card in '%s'", self.reader)

        self.mitm = mitm

        atexit.register(self.cleanup)

    def cleanup(self):
        """
        Close the connection to the physical card
        """
        try:
            self.session.close()
        except smartcard.Exceptions.CardConnectionException as e:
            logging.warning("Error disconnecting from card: %s", str(e))

    def getATR(self):
        # when powerDown has been called, fetching the ATR will throw an error.
        # In this case we must try to reconnect (and then get the ATR).
        try:
            atr = self.session.getATR()
        except smartcard.Exceptions.CardConnectionException as e:
            try:
                # Try to reconnect to the card
                self.session.close()
                self.session = smartcard.Session(self.reader)
                atr = self.session.getATR()
            except smartcard.Exceptions.CardConnectionException as e:
                logging.critical("Error getting ATR: %s", str(e))
                sys.exit()

        return "".join([chr(b) for b in atr])

    def powerUp(self):
        # When powerUp is called multiple times the session is valid (and the
        # card is implicitly powered) we can check for an ATR. But when
        # powerDown has been called, the session gets lost. In this case we
        # must try to reconnect (and power the card).
        try:
            self.session.getATR()
        except smartcard.Exceptions.CardConnectionException as e:
            try:
                self.session = smartcard.Session(self.reader)
            except smartcard.Exceptions.CardConnectionException as e:
                logging.critical("Error connecting to card: %s", str(e))
                sys.exit()

    def powerDown(self):
        # There is no power down in the session context so we simply
        # disconnect, which should implicitly power down the card.
        try:
            self.session.close()
        except smartcard.Exceptions.CardConnectionException as e:
            logging.critical("Error disconnecting from card: %s", str(e))
            sys.exit()

    def reset(self):
        self.powerDown()
        self.powerUp()

    def execute(self, msg):
        # sendCommandAPDU() expects a list of APDU bytes
        if isinstance(msg,str):
            apdu = map(ord, msg)
        else:
            apdu = list(msg)

        apdu = self.mitm.handleInPDU(apdu)

        try:
            rapdu, sw1, sw2 = self.session.sendCommandAPDU(apdu)
        except smartcard.Exceptions.CardConnectionException as e:
            logging.critical("Error transmitting APDU: %s", str(e))
            sys.exit()

        # XXX this is a workaround, see on sourceforge bug #3083586
        # should better use
        # rapdu = rapdu + [sw1, sw2]
        if rapdu[-2:] == [sw1, sw2]:
            pass
        else:
            rapdu = rapdu + [sw1, sw2]

        rapdu = self.mitm.handleOutPDU(rapdu)

        # return the response APDU as string
        return "".join(map(chr, rapdu))
