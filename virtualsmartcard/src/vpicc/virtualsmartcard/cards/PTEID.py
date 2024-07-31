#
# Copyright (C) 2021 João Paulo Barraca
# Copyright (C) 2023 André Guerreiro
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

from virtualsmartcard.SmartcardSAM import SAM
from virtualsmartcard.SWutils import SwError, SW
from virtualsmartcard.TLVutils import pack, unpack, bertlv_pack
from virtualsmartcard.SEutils import ControlReferenceTemplate, \
    Security_Environment
from virtualsmartcard.utils import C_APDU, hexdump
from virtualsmartcard.VirtualSmartcard import Iso7816OS
from virtualsmartcard.SmartcardFilesystem import MF, DF, EF
from virtualsmartcard.ConstantDefinitions import MAX_SHORT_LE
import virtualsmartcard.CryptoUtils as vsCrypto
from virtualsmartcard.utils import inttostring, stringtoint, C_APDU, R_APDU
import logging
from binascii import hexlify, b2a_base64, a2b_base64
import sys
import json

logger = logging.getLogger('pteid')
logger.setLevel(logging.DEBUG)

from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.asymmetric import ec, padding, utils
from cryptography.hazmat.primitives.serialization import load_der_private_key
from cryptography.hazmat.backends import default_backend

class PTEIDOS(Iso7816OS):
    def __init__(self, mf, sam, ins2handler=None, maxle=MAX_SHORT_LE):
        Iso7816OS.__init__(self, mf, sam, ins2handler, maxle)
        self.atr = '\x3B\xFF\x96\x00\x00\x81\x31\xFE\x43\x80\x31\x80\x65\xB0\x85\x04\x01\x20\x12\x0F\xFF\x82\x90\x00\xD0'

    def execute(self, msg):
        logger.debug("Command APDU (%d bytes):\n  %s", len(msg),
                     hexdump(msg, indent=2))
        
        try:
            c = C_APDU(msg)
        except ValueError as e:
            logger.exception(f"Failed to parse {e} APDU {msg}")
            return self.formatResult(False, 0, 0, "",
                                     SW["ERR_INCORRECTPARAMETERS"])
        
        result = ''
        sw = 0x9000

        try:
            logger.debug(f"Handle {hex(c.ins)}")
            sw, result = self.handle_execute(c)

        except SwError as e:
            #logger.error(self.ins2handler.get(c.ins, None))
            logger.exception("SWERROR")
            sw = e.sw
        except Exception as e:
            logger.exception(f"ERROR: {e}")
        if isinstance(result, str):
            result = result.encode()

        logger.debug(f"Result: {hexlify(result)} {hex(sw)}")

        r = self.formatResult(c.ins, c.p1, c.p2, c.le, result, sw)
        return r
    
    def handle_execute(self, c):
        def notImplemented(*argz, **args):
            raise SwError(SW["ERR_INSNOTSUPPORTED"])
        result = ''
        
        if c.ins == 0x80:
            sw, result = self.sam.handle_0x80(c.p1, c.p2, c.data)
        else:
            sw, result = self.ins2handler.get(c.ins, notImplemented)(c.p1,
                                                                        c.p2,
                                                                        c.data)
        return sw, result

    def formatResult(self, ins, p1, p2, le, data, sw):
        logger.debug(
            f"FormatResult: ins={hex(ins)} p1={hex(p1)} p2={hex(p2)} le={le} length={len(data)} sw={hex(sw)}")
        
        if ins == 0xb0 and le == 0 or ins == 0xa4:
            le = min(256, len(data))

        if ins == 0xa4 and len(data):
            self.lastCommandSW = sw
            self.lastCommandOffcut = data
            r = R_APDU(inttostring(SW["NORMAL_REST"] +
                                   min(0xff, len(data) ))).render()
        else:
            
            if le is None:
                le = 0

            r = Iso7816OS.formatResult(self, Iso7816OS.seekable(ins), le,
                                       data, sw, False)
        return r

class PTEIDOS_V2(PTEIDOS):
    def __init__(self, mf, sam, app_ids, ins2handler=None, maxle=MAX_SHORT_LE):
        PTEIDOS.__init__(self, mf, sam, ins2handler, maxle)
        self.app_ids = app_ids
        self.atr = '\x3b\xff\x96\x00\x00\x81\x31\xfe\x43\x80\x31\x80\x65\xb0\x85\x05\x00\x11\x12\x0f\xff\x82\x90\x00\xe1'

    def handle_execute(self, c):
        def notImplemented(*argz, **args):
            raise SwError(SW["ERR_INSNOTSUPPORTED"])
        result = ''

        # intercept select AID's to handle MF swap
        INS_SELECT_AID = c.ins == 0xA4 and c.p1 & 0x4 != 0
        if INS_SELECT_AID and c.data in self.app_ids:
            self.swapMf(self.app_ids[c.data])
            sw = 0x9000

        else:
            sw, result = self.ins2handler.get(c.ins, notImplemented)(c.p1,
                                                                        c.p2,
                                                                        c.data)
        return sw, result

class PTEID_SE(Security_Environment):

    def __init__(self, MF, SAM):
        Security_Environment.__init__(self, MF, SAM)
        logger.debug("Using PTEID SE")
        self.PTEID_ALGORITHMS = {}
        self.PTEID_ALGORITHMS[0x10] = "SHA-1"
        self.PTEID_ALGORITHMS[0x30] = "SHA-224"
        self.PTEID_ALGORITHMS[0x40] = "SHA-256"
        self.PTEID_ALGORITHMS[0x50] = "SHA-384"
        self.PTEID_ALGORITHMS[0x60] = "SHA-512"
        self.PTEID_ALGORITHMS[0x02] = "RSA-PKCS1v15"
        self.PTEID_ALGORITHMS[0x04] = "ECDSA"
        self.PTEID_ALGORITHMS[0x05] = "RSA-PSS"
        self.at.algorithm = 'SHA'
        self.data_to_sign = b''
        self.signature = b''
        self.hash_algorithm = ''
        self.signature_algorithm = ''
        self.key1 = None
        self.key2 = None
        self.key_id = 0

        logger.debug(f"AT: {self.at.algorithm}")

    def parse_SE_config(self, data):
        error = False
        structure = unpack(data)
        for tlv in structure:
            tag, length, value = tlv
            if tag == 0x80:
                if len(value) > 1 or value[0] & 0xF0 not in self.PTEID_ALGORITHMS or value[0] & 0x0F not in self.PTEID_ALGORITHMS:
                    error = True
                    logger.debug(f"Invalid value for tag algo ID: {value}")
                else:
                    self.hash_algorithm = self.PTEID_ALGORITHMS[value[0] & 0xF0]
                    self.signature_algorithm = self.PTEID_ALGORITHMS[value[0] & 0x0F]
                    logger.debug(f"Hash: {self.hash_algorithm} Signature: {self.signature_algorithm}")
            elif tag == 0x84:
                self.key_id = int(value[0])
                self.dst.key = self.key1 if self.key_id == 1 else self.key2
            else:
                error = True

        if error:
            raise SwError(SW["ERR_REFNOTUSABLE"])
        else:
            return SW["NORMAL"], ""

    def __check_dst_input_hash_length(self, length):
        digest_sizes = {20: 'SHA-1', 28: 'SHA-224', 32: 'SHA-256', 48: 'SHA-384', 64: 'SHA-512'}
        try: 
            digest_type = digest_sizes[length]
            return digest_type == self.hash_algorithm
        except KeyError:
            return False

    def manage_security_environment(self, p1, p2, data):
        if p1 != 0x41:
            raise SwError(SW["ERR_INCORRECTP1P2"])
        #TODO: we only support DIGITAL SIGNATURE template for now
        if p2 != 0xB6:
            logger.warning(f'MSE SET unsupported param P2: {p2:2x}')
            raise SwError(SW["ERR_INCORRECTP1P2"])
        return self.parse_SE_config(data)
    
    def __current_hash_algorithm(self):
        if self.hash_algorithm == 'SHA-256':
            return hashes.SHA256()
        elif self.hash_algorithm == 'SHA-384':
            return hashes.SHA384()
        elif self.hash_algorithm == 'SHA-512':
            return hashes.SHA512()

    def compute_digital_signature(self, p1, p2, data):

        """
        Compute a digital signature for the given data.
        Algorithm and key are specified in the current SE
        """
        if self.data_to_sign == b'':
            return self.signature

        logger.debug(f"Compute digital signature p1={hex(p1)} p2={hex(p2)} dsl={len(self.data_to_sign)} ds={hexlify(self.data_to_sign)} d={data}")

        if p1 != 0x9E or p2 != 0x9A:
            raise SwError(SW["ERR_INCORRECTP1P2"])

        if self.dst.key is None:
            raise SwError(SW["ERR_CONDITIONNOTSATISFIED"])

        if self.data_to_sign is None:
            raise SwError(SW["ERR_CONDITIONNOTSATISFIED"])

        # Get the corresponding PIN ID relative to the key_id
        PIN_ID = self.sam.KEY_IDS[self.key_id]

        if not self.sam.verificationStatus(PIN_ID):
            raise SwError(SW["ERR_SECSTATUS"])
        
        logger.debug(f"Current SE contains algo: {self.signature_algorithm} and key_id: {self.key_id}")

        to_sign = self.data_to_sign # Data to be signed

        # Get Key type of our private key
        try:
            ec_curve = self.dst.key.curve
            is_ecdsa = True
        except AttributeError:
            is_ecdsa = False
        
        if is_ecdsa and self.signature_algorithm != "ECDSA":
            raise SwError(SW["ERR_CONDITIONNOTSATISFIED"])
        if not is_ecdsa and self.signature_algorithm == "ECDSA":
            raise SwError(SW["ERR_CONDITIONNOTSATISFIED"])

        if is_ecdsa:
            logger.debug(f"Using private key of elliptic curve: {ec_curve}")
            self.signature = bytes(self.dst.key.sign(
                to_sign,
                ec.ECDSA(utils.Prehashed(self.__current_hash_algorithm()))
            ))
        else:
            self.signature = bytes(self.dst.key.sign(
                to_sign,
                padding.PKCS1v15(),
                utils.Prehashed(self.__current_hash_algorithm())
                ))
        
        self.sam.resetVerificationStatus(PIN_ID)

        logger.debug(f"Signature: {hexlify(self.signature)}")
        return self.signature

    def hash(self, p1, p2, data):
        """
        Hash the given data using the algorithm specified by the current
        Security environment.

        :return: raw data (no TLV coding).
        """
        logger.debug(f"Compute Hash {hex(p1)} {hex(p2)} {hexlify(data)}")

        if p1 != 0x90 or p2 not in (0x80, 0xA0):
            raise SwError(SW["ERR_INCORRECTP1P2"])
        #Most common case: hash performed externally
        if p2 == 0xA0:
            tlv_list = unpack(data)
            tag, length, value = tlv_list[0]
            #Tag 90 is required for the input data template
            if tag == 0x90:
                hash_data = value
                if not self.__check_dst_input_hash_length(length):
                    raise SwError(SW["ERR_CONDITIONNOTSATISFIED"])
                logger.debug(f"Hash_data: {hexlify(hash_data)}")
                self.data_to_sign = hash_data
            else:
                raise SwError(SW["ERR_INCORRECTPARAMETERS"])
        #TODO: Hash performed totally or partially by the card

        return hash_data

class PTEID_SAM(SAM):
    def __init__(self, mf=None, auth_private_key=None, sign_private_key=None):
        SAM.__init__(self, None, None, mf, default_se=PTEID_SE)
        self.current_SE = self.default_se(self.mf, self)
        #TODO: read PIN values from card.json
        self.AUTH_PIN_ID = 0x81
        self.SIGN_PIN_ID = 0x82
        self.ADDR_PIN_ID = 0x83

        self.AUTH_KEY_ID = 2
        self.SIGN_KEY_ID = 1

        self.KEY_IDS = {}
        self.KEY_IDS[self.AUTH_KEY_ID] = self.AUTH_PIN_ID
        self.KEY_IDS[self.SIGN_KEY_ID] = self.SIGN_PIN_ID

        self.PIN_INFO = {}
        self.PIN_INFO[self.AUTH_PIN_ID] = {'value': b'1111', 'verified': False, 'counter': 3}
        self.PIN_INFO[self.SIGN_PIN_ID] = {'value': b'1234', 'verified': False, 'counter': 3}
        self.PIN_INFO[self.ADDR_PIN_ID] = {'value': b'0000', 'verified': False, 'counter': 3}

        self.current_SE.ht.algorithm = "SHA"
        self.current_SE.algorithm = "AES-CBC"

        self.current_SE.key1 = load_der_private_key(sign_private_key, password=None, backend=default_backend())
        self.current_SE.key2 = load_der_private_key(auth_private_key, password=None, backend=default_backend())

    def getCurrentApplication(self):
        return self.mf.identifier

    def change_reference_data(self, p1, p2, data):
        self.verify(p1, p2, data[:4])

        self.PIN_INFO[p2]['value'] = data[8:12]
        self.resetVerificationStatus(p2);
        return SW["NORMAL"], ""

    def handle_0x80(self, p1, p2, data):
        logger.debug(f"Handle 0x80 {hex(p1)} {hex(p2)} {hex(data)}")
        sys.exit(-1)
        return 0x9000, b''

    def parse_SE_config(self, config):
        r = 0x9000
        logger.debug(type(config))
        logger.debug(f"Parse SE config {hexlify(config)}")

        try:
            ControlReferenceTemplate.parse_SE_config(self, config)
        except SwError as e:
            logger.exception("e")

        return r, b''

    def verificationStatus(self, id):
        return self.PIN_INFO[id]['verified']

    def resetVerificationStatus(self, id):
        self.PIN_INFO[id]['verified'] = False

    def verify(self, p1, p2, PIN):
        PIN = PIN.replace(b"\xFF", b"")        # Strip \xFF characters
        logger.debug("PIN to use: %s", PIN)

        pin_info = self.PIN_INFO[p2]

        #A VERIFY command without PIN value means GET RETRY counter
        if len(PIN) == 0:
            return 0x63C0 | pin_info['counter'], ""
        if pin_info['counter'] > 0:
            #XX: The unblock PINs actually have 5 retries
            if pin_info['value'] == PIN:
                pin_info['counter'] = 3
                pin_info['verified'] = True
                return SW["NORMAL"], ""
            else:
                pin_info['counter'] -= 1
                pin_info['verified'] = False
                return 0x63C0 | pin_info['counter'], ""
        else:
            raise SwError(SW["ERR_AUTHBLOCKED"])

class PTEID_SAM_V2(PTEID_SAM):
    def __init__(self, mf=None, auth_private_key=None, sign_private_key=None):
        PTEID_SAM.__init__(self, mf, auth_private_key, sign_private_key)
        self.AUTH_KEY_ID = 6
        self.SIGN_KEY_ID = 8
        
        self.KEY_IDS[self.AUTH_KEY_ID] = self.AUTH_PIN_ID
        self.KEY_IDS[self.SIGN_KEY_ID] = self.SIGN_PIN_ID

    def change_reference_data(self, p1, p2, data):
        if self.getCurrentApplication() != "EID":
            raise SwError(SW["ERR_INSNOTSUPPORTED"])
        return super().change_reference_data(p1, p2, data)
    
    def verificationStatus(self, id):
        if self.getCurrentApplication() != "EID":
            raise SwError(SW["ERR_INSNOTSUPPORTED"])
        return super().verificationStatus(id)
    
    def resetVerificationStatus(self, id):
        if self.getCurrentApplication() != "EID":
            raise SwError(SW["ERR_INSNOTSUPPORTED"])
        return super().resetVerificationStatus(id)
    
    def verify(self, p1, p2, PIN):
        if self.getCurrentApplication() != "EID":
            raise SwError(SW["ERR_INSNOTSUPPORTED"])
        return super().verify(p1, p2, PIN)
class PTEID_MF(MF):  # {{{
    def getDataPlain(self, p1, p2, data):

        logger.debug(
            f"GetData Plain {hex(p1)} {hex(p2)} {hexlify(data)}")

        tag = (p1 << 8) + p2
        if tag == 0xDF03:
            return 0x6E00, b''
        elif tag == 0xDF30:      #Applet version info: hardcoded IAS v 4.4.2
            return 0x9000, b'\xDF\x30\x07\x34\x2E\x34\x2E\x32\x2E\x41'
        elif tag == 0x9F7F:      #CPLC info consistent with IAS 5.0 test cards
            return 0x9000, b'\x9F\x7F\x2A\x40\x90\x00\x39\x19\x81\x10\x55\x05\x00\x31\x24\x1E\x01\xC6\x68\xB0\x79\x12\x92\x31\x24\x12\x93\x31\x24\x12\x94\x31\x24\x00\x00\x00\x20\x00\x00\x00\x00\x00\x00\x00\x00'
        else:
            logger.warning(f"Unsupported tag in GET DATA cmd: {tag:4X}")
            raise SwError(SW["ERR_INCORRECTP1P2"])

    def readBinaryPlain(self, p1, p2, data):
        logger.debug(f"Read Binary P1={hex(p1)} P2={hex(p2)} {data}")
        ef, offsets, datalist = self.dataUnitsDecodePlain(p1, p2, data)
        logger.debug(f"EF={ef} offsets={offsets} datalist={datalist}")

        try:
            sw, result = super().readBinaryPlain(p1, p2, data)
            return 0x9000, result
        except Exception as e:
            logger.exception(f"{e}")
            raise


    def selectFile(self, p1, p2, data):
        """
        Function for instruction 0xa4. Takes the parameter bytes 'p1', 'p2' as
        integers and 'data' as binary string. Returns the status bytes as two
        byte long integer and the response data as binary string.
        """
        logger.debug(f"SelectFile: fid=0x{hexlify(data).decode('latin')} p2={p2}")

        P1_MF_DF_EF = p1 == 0
        P1_CHILD_DF = p1 & 0x01 == 0x01
        P1_EF_IN_DF = p1 & 0x02 == 0x02
        P1_PARENT_DF = p1 & 0x03 == 0x03
        P1_BY_DFNAME = p1 & 0x4 != 0 
        P1_DIRECT_BY_DFNAME = p1 & 0x7 == 0x04
        P1_BY_PATH = p1 & 0x8 != 0
        P1_FROM_MF = p1 & 0xf == 0x08
        P1_FROM_CURR_DF = p1  & 0xf == 0x09

        P2_FCI = p2 & 0x0C == 0
        P2_FCP = p2 & 0x04 != 0
        P2_FMD = p2 & 0x08 != 0
        P2_NONE = p2 & 0x0C != 0


        logger.debug(f"P1 - MF_DF_EF:{P1_MF_DF_EF} CHILD_DF:{P1_CHILD_DF} EF_IN_DF:{P1_EF_IN_DF} PARENT_DF:{P1_PARENT_DF} BY_DFNAME:{P1_BY_DFNAME} DIR_BY_DFNAME:{P1_DIRECT_BY_DFNAME} BY_PATH:{P1_BY_PATH} FROM_MF:{P1_FROM_MF} FROM_CUR_DF:{P1_FROM_CURR_DF}")
        logger.debug(f"P2 - FCI:{P2_FCI}, FCP:{P2_FCP} FMD:{P2_FMD} NONE:{P2_NONE}")
       
        # Patch instruction to Find MF to replicate PTEID behavior
        if data == b'\x4f\x00':
            p1 |= 8

        # Will fail with exception if File Not Found
        file = self._selectFile(p1, p2, data)
        self.current = file
        extra = b''
       
        if P2_NONE:
            pass
        elif P2_FCI:
            extra = self.get_fci(file)
            logger.debug(f"FCI: {extra}")
        else:
            extra = b''
    
        
        if isinstance(file, EF):
            logger.debug("IS EF")

        elif isinstance(file, DF):
            logger.debug("IS DF")
        
        return 0x9000, extra

    def get_fci(self, file):
        try:
            if isinstance(file, EF):
                fcid = b'\x6F\x15' + \
                    b'\x81\x02' + len(file.data).to_bytes(2, byteorder='big') + \
                    b'\x82\x01\x01' +  \
                    b'\x8a\x01\x05' +\
                    b'\x83\x02' + file.fid.to_bytes(2, byteorder='big')+ \
                    file.extra_fci_data
            else:
                fcid = b'\x6F\x14' + \
                    b'\x83\x02' + file.fid.to_bytes(2, byteorder='big') + \
                    file.extra_fci_data
                logger.debug(f"FCI Data: {file.extra_fci_data}")
                name = getattr(file, 'dfname')
                if len(name) > 0:
                    fcid = fcid + b'\x84' + len(name).to_bytes(1, byteorder='big') + name

            return fcid
        except Exception as e:
            logger.exception(f"get fci: {e}")
            return b''

# }}}
