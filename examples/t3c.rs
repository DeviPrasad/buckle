/*
    Copyright 2024 M. Devi Prasad

    Licensed under the Apache License, Version 2.0 (the "License");
    you may not use this file except in compliance with the License.
    You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

    Unless required by applicable law or agreed to in writing, software
    distributed under the License is distributed on an "AS IS" BASIS,
    WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
    See the License for the specific language governing permissions and
    limitations under the License.
*/

use std::io;
use std::net::ToSocketAddrs;

use tokio::io::AsyncWriteExt;
use tokio::net::{TcpSocket, TcpStream};

use buckle::init_logger;

use crate::tls3::{AlertDesc, CipherSuite, ClientHelloHandshake, Extension, ServerHelloHandshake};

#[allow(dead_code)]
pub mod tls3 {
    use bytes::Bytes;

    pub type ProtoColVersion = u16;
    pub type Random = [u8; 32];

    pub type CipherSuiteRaw = (u8, u8);

    #[repr(u8)]
    #[derive(Clone, Debug)]
    pub enum CipherSuite {
        TlsAes128GcmSha256,
        TlsAes256GcmSha384,
        TlsChacha20Poly1305Sha256,
    }

    impl TryFrom<(u8, u8)> for CipherSuite {
        type Error = RecErr;

        fn try_from(value: (u8, u8)) -> Result<Self, Self::Error> {
            match value {
                (0x13, 0x01) => Ok(CipherSuite::TlsAes128GcmSha256),
                (0x13, 0x02) => Ok(CipherSuite::TlsAes256GcmSha384),
                (0x13, 0x03) => Ok(CipherSuite::TlsChacha20Poly1305Sha256),
                _ => Err(RecErr::CipherUnsupported)
            }
        }
    }

    impl Into<CipherSuiteRaw> for CipherSuite {
        fn into(self) -> CipherSuiteRaw {
            match self {
                CipherSuite::TlsAes128GcmSha256 => (0x13, 0x01),
                CipherSuite::TlsAes256GcmSha384 => (0x13, 0x02),
                CipherSuite::TlsChacha20Poly1305Sha256 => (0x13, 0x03),
            }
        }
    }

    pub const LEGACY_VER_0X0303: u16 = (0x03_u16 << 8) | 0x3;
    pub const REC_SIZE_BYTES_MAX: usize = 1 << 14;

    #[repr(u8)]
    #[derive(Clone, Debug, PartialEq)]
    pub enum ContentType {
        Invalid = 0,
        ChangeCipherSpec = 20,
        Alert = 21,
        Handshake = 22,
        ApplicationDate = 23,
        _Unused_ = 255
    }

    #[repr(u8)]
    #[derive(Clone, Debug, PartialEq)]
    pub enum HandshakeType {
        ClientHello = 1,
        ServerHello = 2,
        NewSessionTicket = 4,
        EndOfEarlyData = 5,
        EncryptedExtensions = 8,
        Certificate = 11,
        CertificateRequest = 13,
        CertificateVerify = 15,
        Finished = 20,
        KeyUpdate = 24,
        MessageHash = 254,
        _Unused_ = 255
    }

    #[repr(u16)]
    #[derive(Clone, Debug, PartialEq, Copy)]
    pub enum ExtensionTypeCode {
        ServerName = 0,
        MaxFragmentLength = 1,
        StatusRequest = 5,
        SupportedGroups = 10,
        ECPointFormats = 11,
        SignatureAlgorithms = 13,
        UseSrtp = 14,
        Heartbeat = 15,
        ApplicationLayerProtocolNegotiation = 16,
        SignedCertificateTimestamp = 18,
        ClientCertificateType = 19,
        ServerCertificateType = 20,
        Padding = 21,
        EncryptThenMAC = 22,
        ExtendedMasterSecret = 23,
        SessionTicket = 35,
        PreSharedKeys = 41,
        EarlyData = 42,
        SupportedVersions = 43,
        Cookie = 44,
        PskKeyExchangeModes = 45,
        CertificateAuthorities = 47,
        OidFilters = 48,
        PostHandshakeAuth = 49,
        SignatureAlgorithmsCert = 50,
        KeyShare = 51,
        Bad = 65535
    }

    #[repr(u8)]
    #[derive(Clone, Debug, PartialEq)]
    pub enum AlertDesc {
        CloseNotify = 0,
        RecordOverflow = 22,
        HandshakeFailure = 40,
        DecodeError = 50,
        ProtocolVersion = 70,
        InsufficientSecurity = 71,
        InternalError = 80,
        MissingExtension = 109,
        UnsupportedExtension = 110,
        Bad = 255,
    }

    impl TryFrom<u8> for AlertDesc {
        type Error = RecErr;

        fn try_from(desc: u8) -> Result<Self, Self::Error> {
            match desc {
                0 => Ok(AlertDesc::CloseNotify),
                22 => Ok(AlertDesc::RecordOverflow),
                40 => Ok(AlertDesc::HandshakeFailure),
                50 => Ok(AlertDesc::DecodeError),
                70 => Ok(AlertDesc::ProtocolVersion),
                71 => Ok(AlertDesc::InsufficientSecurity),
                80 => Ok(AlertDesc::InternalError),
                109 => Ok(AlertDesc::MissingExtension),
                110 => Ok(AlertDesc::UnsupportedExtension),
                _ => Err(RecErr::UnknownAlertDesc),
            }
        }
    }

    pub type KeyShareExtData<'a> = (usize, &'a [u8]);

    #[derive(Clone, Debug)]
    pub enum ExtensionType {
        Ed25519KeyShare([u8; 32]),
        SupportedVersionTls13,
    }

    impl ExtensionTypeCode {
        fn from((u, v): (u8, u8)) -> Result<Self, RecErr> {
            match (u, v) {
                (0, 0) => Ok(Self::ServerName),
                (0, 10) => Ok(Self::SupportedGroups),
                (0, 11) => Ok(Self::ECPointFormats),
                (0, 13) => Ok(Self::SignatureAlgorithms),
                (0, 16) => Ok(Self::ApplicationLayerProtocolNegotiation),
                (0, 17) => Ok(Self::ExtendedMasterSecret),
                (0, 22) => Ok(Self::EncryptThenMAC),
                (0, 23) => Ok(Self::ExtendedMasterSecret),
                (0, 35) => Ok(Self::SessionTicket),
                (0, 43) => Ok(Self::SupportedVersions),
                (0, 45) => Ok(Self::PskKeyExchangeModes),
                (0, 51) => Ok(Self::KeyShare),
                _ => {
                    log::error!("ExtensionType - error. Unsupported type {v}");
                    Err(RecErr::UnsupportedExtension)
                }
            }
        }
    }

    pub struct CipherSuites {}

    impl CipherSuites {
        pub fn deserialize(bytes: &[u8]) -> Result<(Vec<CipherSuite>, usize), RecErr> {
            let mut i: usize = 0;
            // cipher suites - len followed by identifiers; sequence of byte-pairs.
            let cipher_suite_len: usize = ((bytes[i] as usize) << 8) | bytes[i + 1] as usize;
            if (cipher_suite_len & 1 == 1) || !(2..=8).contains(&cipher_suite_len) {
                return Err(RecErr::CipherSuiteLen)
            }
            i += 2;
            let mut cipher_suites: Vec<Option<CipherSuite>> = vec![None, None, None, None, None, ];
            for k in (0..cipher_suite_len).step_by(2) {
                let cm = bytes[i + k];
                let cl = bytes[i + 1 + k];
                let rcs = CipherSuite::try_from((cm, cl));
                if let Ok(cs) = rcs {
                    if cipher_suites[cl as usize].is_some() {
                        return Err(RecErr::CipherDuplicate)
                    } else {
                        cipher_suites[cl as usize] = Some(cs)
                    }
                }
            }
            let res: Vec<CipherSuite> = vec![];
            Ok((res, cipher_suite_len + 2))
        }

        pub fn valid(cipher: CipherSuiteRaw) -> Result<CipherSuite, RecErr> {
            /*log::info!("valid_cipher: ({:x},{:x})", cipher.0, cipher.1);
            if !(cipher.0 == 0x13 && (0..=5).contains(&cipher.1)) {
                return Err(RecErr::CipherUnsupported)
            }
            Ok(cipher)*/
            CipherSuite::try_from(cipher)
        }
    }

    #[derive(Clone, Copy, Debug)]
    pub struct Extension<'a> {
        xtc: ExtensionTypeCode,
        data: Option<&'a [u8]>,
    }

    struct Extensions {}

    impl Extensions {
        fn deserialize(bytes: &[u8]) -> Result<(Vec<Extension>, usize), RecErr> {
            let mut i: usize = 0;
            // extensions - length in two bytes
            let ext_len: usize = ((bytes[i] as usize) << 8) | bytes[i + 1] as usize;
            // look for at least one extension: Supported Versions
            // log::info!("ext_len = {ext_len}, i = {i}");
            // log::info!("extensions = {:#?}", &bytes[2..34]);
            if ext_len < 7 || i + ext_len > bytes.len() {
                return Err(RecErr::ExtensionLen)
            }
            i += 2;
            // extensions - data
            let mut extensions: Vec<Extension> = vec![];
            loop {
                if let Ok((ext, len)) = Extension::deserialize(bytes, i) {
                    i += len;
                    let key_share = ext.key_share();
                    extensions.push(ext);
                    if key_share {
                        break
                    }
                }
            }
            Ok((extensions, i + ext_len))
        }

        fn size(extensions: &[Extension]) -> usize {
            extensions.iter().fold(0, |acc, ext| acc + ext.size())
        }
    }

    impl<'a> Extension<'a> {
        pub fn server_name(name: &'a str) -> Self {
            Extension {
                xtc: ExtensionTypeCode::ServerName,
                data: Some(name.as_bytes())
            }
        }

        pub fn session_null_ticket() -> Self {
            Extension {
                xtc: ExtensionTypeCode::SessionTicket,
                data: Some(&[0, 35, 0, 0])
            }
        }

        pub fn supported_ver_1_3() -> Self {
            Extension {
                xtc: ExtensionTypeCode::SupportedVersions,
                data: Some(&[0x00, 0x2b, 0x00, 0x03, 0x02, 0x03, 0x04])
            }
        }

        pub fn ed25519_key_share(data: &'a [u8; 32]) -> Self {
            Extension {
                xtc: ExtensionTypeCode::KeyShare,
                data: Some(data.as_slice())
            }
        }

        pub fn supported_group_x25519() -> Self {
            Extension {
                xtc: ExtensionTypeCode::SupportedGroups,
                data: None,
            }
        }

        pub fn signature_algorithm_ed25519() -> Self {
            Extension {
                xtc: ExtensionTypeCode::SignatureAlgorithms,
                data: None,
            }
        }

        fn key_share(&self) -> bool {
            self.xtc == ExtensionTypeCode::KeyShare
        }

        fn verify(&self) -> Result<&Self, RecErr> {
            if self.xtc == ExtensionTypeCode::SupportedVersions && self.data != Some(&[0x03_u8, 0x04]) {
                Err(RecErr::UnsupportedVersion)
            } else {
                Ok(self)
            }
        }
        fn size(&self) -> usize {
            match self.xtc {
                ExtensionTypeCode::SupportedVersions => 7,
                // ed25519 key is 32 bytes + 10 bytes prefix describing the key share
                ExtensionTypeCode::KeyShare => 42,
                ExtensionTypeCode::SupportedGroups => 10,
                ExtensionTypeCode::SignatureAlgorithms => 12,
                ExtensionTypeCode::ServerName => {
                    let sn = self.data.expect("server name is mandatory for TLS 1.3");
                    sn.len() + 9
                },
                ExtensionTypeCode::SessionTicket => 4,
                _ => {
                    panic!("Extension.size for unknown type!!");
                },
            }
        }

        fn deserialize(bytes: &'a [u8], start: usize) -> Result<(Extension<'a>, usize), RecErr> {
            let mut i = start;
            let xtc = (bytes[i], bytes[i + 1]);
            /*if xt_type.0 != 0 {
                eprintln!("extension type error? ==> {xt_type:?}");
                return Err(RecErr::ExtensionType)
            }*/
            let ext_type_code = ExtensionTypeCode::from(xtc)?;
            // eprintln!("extension type ==> {xt_type:?} ==> {ext_type:?}");
            i += 2;
            let xt_total_len = ((bytes[i] as usize) << 8) | bytes[i + 1] as usize;
            i += 2;
            if xt_total_len == 0 {
                return Ok((Extension {
                    xtc: ext_type_code,
                    data: None,
                }, i - start))
            }
            let xt_data_len: usize;
            (xt_data_len, i) = if ext_type_code == ExtensionTypeCode::SupportedVersions {
                if bytes[i] == 0 {
                    (bytes[i + 1] as usize, i + 2)
                } else {
                    (bytes[i] as usize, i)
                }
            } else if ext_type_code == ExtensionTypeCode::ECPointFormats ||
                ext_type_code == ExtensionTypeCode::PskKeyExchangeModes {
                (bytes[i] as usize, i + 1)
            } else {
                (((bytes[i] as usize) << 8) | bytes[i + 1] as usize, i + 2)
            };
            if xt_data_len == 0 {
                return Err(RecErr::ExtensionData)
            }
            // 'xt_data_len' > 0 and 'i' is at the first byte of the extension data.
            let k = i + (xt_data_len - 1);
            let ext: Extension = *Extension {
                xtc: ext_type_code,
                data: Some(bytes[i..k].iter().as_slice()),
            }.verify()?;

            Ok((ext, k - start))
        }

        pub fn serialize(&self, bytes: &'a mut [u8], i: usize) -> usize {
            match self.xtc {
                ExtensionTypeCode::ServerName => {
                    let sn = self.data.expect("server name is mandatory for TLS 1.3");
                    let snl = sn.len() as u8;
                    bytes[i..i + 9 + snl as usize].copy_from_slice(
                        &[[0, 0, 0, snl + 5, 0, snl + 3, 0, 0, snl].as_slice(), sn].concat());
                    (9 + snl) as usize
                },

                ExtensionTypeCode::SessionTicket => {
                    let st = self.data.expect("session ticket missing.");
                    bytes[i..i + 4].copy_from_slice(st);
                    st.len()
                },

                ExtensionTypeCode::SupportedVersions => {
                    bytes[i..i + 7].copy_from_slice(&[0x00, 0x2b, 0x00, 0x03, 0x02, 0x03, 0x04]);
                    7
                },

                ExtensionTypeCode::KeyShare => {
                    if let Some(key) = self.data {
                        let len = key.len() as u8;
                        bytes[i..i + 10].copy_from_slice(&[
                            0, 51, // extension "Key Share"
                            0, len + 6, // 38 bytes of "Key Share" extension data follows
                            0, len + 4, // 36 bytes of key share data follows
                            0, 29, // value for x25519 (key exchange via curve25519)
                            0, len, // 32 bytes of public key follows
                        ]);
                        bytes[i + 10..i + 10 + len as usize].copy_from_slice(key);
                        len as usize + 10
                    } else {
                        0
                    }
                },

                ExtensionTypeCode::SupportedGroups => {
                    let n = 10u8;
                    bytes[i..i + n as usize].copy_from_slice(&[
                        0, 0x0a, // extension "Supported Groups"
                        0, n - 4, // 4 bytes of "Supported Groups" extension data follows
                        0, n - 6, // 2 bytes of the curve data follows
                        0, 0x1d, // value for the curve x25519
                        0, 0x17, // value for the curve secp256r1
                    ]);
                    n as usize
                },

                // page 102, section 9.1, Mandatory-to-implement cipher suites.
                // 'mozilla.org', 'yourdot.net', 'usa.gov' require the following two algorithms.
                // MUST support RSA-PSS-RSAE-SHA256 for CertificateVerify and certificates.
                // MUSt support ECDSA-SECP256r1-SHA256.
                // MUST support RSA-PKCS1-SHA256 for certificates.
                ExtensionTypeCode::SignatureAlgorithms => {
                    let n = 12u8;
                    bytes[i..i + n as usize].copy_from_slice(&[
                        0, 0x0d, // extension "Signature Algorithms""
                        0, n - 4, // 4 bytes of "Signature Algorithms" extension data follows
                        0, n - 6, // 2 bytes of the algorithm identifier
                        8, 7, // value for the ED25519
                        4, 3, // value for the ECDSA-SECP256r1-SHA256
                        8, 4, // value for RSA-PSS-RSAE-SHA256
                        //4, 1, // value for RSA-PKCS1-SHA256
                    ]);
                    n as usize
                }
                _ => 0
            }
        }
    }

    struct CompressionMethods {}

    impl CompressionMethods {
        pub fn deserialize(bytes: &[u8]) -> Result<usize, RecErr> {
            // compression methods
            if !(bytes[0] == 1 && bytes[1] == 0) {
                return Err(RecErr::CompressionMethods)
            }
            Ok(2)
        }
    }

    #[derive(Clone, Debug)]
    pub struct ClientHelloHandshake<'a> {
        // TLSPlainText; page 79, sec 5.1. Record Layer
        rct: ContentType, // record content type - Handshake(22)
        // TLS 1.3 has deprecated the legacy record version indicator.
        // It MUST be set to 0x0303, and ignored for all practical purposes.
        legacy_rec_ver: ProtoColVersion, // lvalue: u16 = 0x0303
        fragment_len: u16,
        // Handshake; Page 25, sec 4. Handshake Protocol
        ht: HandshakeType, // handshake type is ClientHello(1)
        len: u32,
        // ClientHello, page 28, sec 4.1.2. Client Hello
        legacy_tls_ver: ProtoColVersion, // value: u16 == 0x0303
        random: Random,
        legacy_session_id: Option<&'a [u8]>, // if [1, 0]
        // B.4. Cipher Suites. Use AES and/or CHACHA20,.
        // TlsAes128GcmSha256 (0x13, 0x01)
        // TlsAes256GcmSha384 (0x13, 0x02)
        // TLS_CHACHA20_POLY1305_SHA256 (0x13, 0x03)
        cipher_suite: Vec<CipherSuite>,
        // size 1 to 255.
        legacy_compression_methods: [u8; 2], // value == [1, 0]
        extensions: Vec<Extension<'a>>,
    }

    #[allow(dead_code)]
    impl<'a> ClientHelloHandshake<'a> {
        pub fn new_with_len(rec_frag_len: u16, random: Random, sid: Option<&'a [u8]>, ciphers: Vec<CipherSuite>, extensions: Vec<Extension<'a>>) -> Self {
            ClientHelloHandshake {
                rct: ContentType::Handshake,
                legacy_rec_ver: LEGACY_VER_0X0303,
                fragment_len: rec_frag_len,
                ht: HandshakeType::ClientHello,
                len: (rec_frag_len - 4) as u32,
                legacy_tls_ver: LEGACY_VER_0X0303,
                random,
                legacy_session_id: sid,
                cipher_suite: ciphers,
                legacy_compression_methods: [1, 0], // no legacy compression methods in TLS 1.3
                extensions,
            }
        }

        pub fn new(random: Random, ciphers: Vec<CipherSuite>, extensions: Vec<Extension<'a>>) -> Result<Self, RecErr> {
            let ch_data_len =
                48 +
                    ciphers.len() * 2 +
                    4 +
                    Extensions::size(&extensions);
            if ch_data_len >= (1 << 14) + 3 {
                return Err(RecErr::TooBig);
            }
            Ok(ClientHelloHandshake {
                rct: ContentType::Handshake,
                legacy_rec_ver: LEGACY_VER_0X0303,
                fragment_len: (ch_data_len - 3) as u16,
                ht: HandshakeType::ClientHello,
                len: (ch_data_len - 9) as u32,
                legacy_tls_ver: LEGACY_VER_0X0303,
                random,
                legacy_session_id: Some(&[2, 1, 0]),
                cipher_suite: ciphers,
                legacy_compression_methods: [1, 0], // no legacy compression methods in TLS 1.3
                extensions,
            })
        }

        fn size(&self) -> usize {
            // each cipher_suite value takes two bytes when serialized
            let cipher_suite_len: usize = 2 * self.cipher_suite.len();
            let ext_len: usize = self.extensions.iter().fold(0, |acc, ext| acc + ext.size());

            1 + // 0: content_type
                2 + // 1: legacy_rec_version
                2 + // 3: fragment_len
                1 + // 5: handshake_type = client_hello == 1
                3 + // 6: message_len = (fragment_len - 4)
                2 + // 9: legacy_version
                32 + // 11: random
                1 + // 43: session_id_len = 0. In our implementation, value == 0
                2 + // 44: cipher_suite_len; uses 2 bytes (u16)
                cipher_suite_len + // 46: lis_of(cipher_suite) -- cipher_suite_len bytes
                2 + // (46 + cipher_suite_len): compression_methods = (1, 0)
                2 + // (46 + cipher_suite_len + 2): ext_len
                ext_len // (46 + cipher_suite_len + 2 + 2): list_of(extension)
        }

        pub fn serialize(&self, bytes: &'a mut [u8]) -> Result<usize, RecErr> {
            // first five bytes of the message hold content_type, legacy_version, and fragment_len.
            let frag_len: u16 = self.size() as u16 - 5;
            bytes[0..3].copy_from_slice(&[
                22, // 0: content_type = handshake
                0x3, 0x03 // 1: legacy_record_version
            ]);
            // 3: fragment_len
            bytes[3..5].copy_from_slice(&frag_len.to_be_bytes());
            let mut i: usize = 5;
            // 5: handshake_type; client_hello == 1
            bytes[i] = 1;
            i += 1;
            // 6: message_len - 3 bytes.
            bytes[i] = 0;
            bytes[i + 1..i + 3].copy_from_slice(&(frag_len - 4).to_be_bytes());
            i += 3;
            // 9: legacy_version
            (bytes[i], bytes[i + 1]) = (3, 3);
            i += 2;
            // 11: random
            for x in 0..32_u8 {
                bytes[i + x as usize] = x + 100;
            }
            i += 32;
            // 43: session_id = (0) - essentially an empty session id.
            bytes[i] = 0;
            i += 1;
            // 46: (0, cipher_suite_len,0x13, 0x3, 0x13, 0x1, 0x13, 0x2) - CHACHA20, AES128, AES256
            bytes[i..i + 8].copy_from_slice(&[0, 6, 0x13, 0x3, 0x13, 0x1, 0x13, 0x2]);
            // (bytes[i], bytes[i + 1], bytes[i + 2], bytes[i + 3], bytes[i + 4], bytes[i + 5], bytes[i + 6], bytes[i + 7]) = (0, 6, 0x13, 0x3, 0x13, 0x1, 0x13, 0x2);
            i += 8;
            // 50: compression_methods = (1, 0)
            (bytes[i], bytes[i + 1]) = (1, 0);
            // 51: extensions_len (2 bytes)
            i += 2;
            let k = i;
            i += 2;
            // 53: extensions
            for ext in self.extensions.iter() {
                i += ext.serialize(bytes, i);
            }
            (bytes[k], bytes[k + 1]) = (0, (i - k - 2) as u8);
            Ok(i)
        }

        pub fn deserialize(bytes: &'a [u8]) -> Result<ClientHelloHandshake<'a>, RecErr> {
            let mut i: usize = 0;
            if bytes[i] != ContentType::Handshake as u8 {
                return Err(RecErr::RecType)
            }
            i += 1; // 1
            if (((bytes[i] as u16) << 8) | bytes[i + 1] as u16) != LEGACY_VER_0X0303 {
                return Err(RecErr::LegacyRecordVer)
            }
            i += 2; // 3
            let frag_len: usize = ((bytes[i] as usize) << 8) | bytes[i + 1] as usize;
            if !(64..=REC_SIZE_BYTES_MAX).contains(&frag_len) {
                return Err(RecErr::FragmentLen)
            }
            i += 2; // 5
            assert_eq!(bytes.len() - 5, frag_len);
            log::info!("frag_len = {frag_len}");
            if bytes[i] != HandshakeType::ClientHello as u8 {
                return Err(RecErr::HandshakeType)
            }
            i += 1; // 6
            let msg_len: usize = ((bytes[i] as usize) << 16) | ((bytes[i + 1] as usize) << 8) | (bytes[i + 2] as usize);
            if !(64..=REC_SIZE_BYTES_MAX).contains(&msg_len) {
                return Err(RecErr::MsgLen)
            }
            assert_eq!(frag_len - 4, msg_len);
            i += 3; // 9
            log::info!("msg_len = {msg_len}");
            if (((bytes[i] as u16) << 8) | bytes[i + 1] as u16) != LEGACY_VER_0X0303 {
                return Err(RecErr::LegacyTLS13MsgVer)
            }
            i += 2; // 11
            let random: &[u8] = &bytes[i..i + 32];
            i += 32; // 43
            let sid_len: u8 = bytes[i];
            log::info!("session_id_len = {sid_len}");
            if sid_len > 32 {
                return Err(RecErr::SessionIdLen)
            }
            // copy session_id including its length
            let sid =
                if sid_len > 0 {
                    Some(&bytes[i..(i + sid_len as usize)])
                } else {
                    None
                };
            i += (sid_len + 1) as usize;

            // cipher suites - len followed by identifiers; sequence of byte-pairs.
            let (cipher_suites, cipher_suite_len) = CipherSuites::deserialize(&bytes[i..])?;
            i += cipher_suite_len;

            i += CompressionMethods::deserialize(&bytes[i..i + 2])?;

            let (extensions, ext_len) = Extensions::deserialize(&bytes[i..])?;
            i += ext_len;

            assert_eq!(i, frag_len + 5);
            Ok(ClientHelloHandshake::new_with_len((frag_len & 0xFFFF) as u16,
                                                  Random::try_from(random).unwrap(),
                                                  sid,
                                                  cipher_suites,
                                                  extensions))
        }
    }

    #[allow(dead_code)]
    #[derive(Debug)]
    pub struct ServerHelloHandshake<'a> {
        // TLSPlainText; page 79, sec 5.1. Record Layer
        rct: ContentType, // record content type - Handshake(22)
        // TLS 1.3 has deprecated the legacy record version indicator.
        // It MUST be set to 0x0303, and ignored for all practical purposes.
        legacy_rec_ver: ProtoColVersion, // legacy record version; value: u16 = 0x0303
        pub(crate) fragment_len: u16,
        // Handshake; Page 25, sec 4. Handshake Protocol
        ht: HandshakeType, // handshake type is ServerHello(2)
        pub(crate) len: u32,
        // ServerHello, page 31, sec 4.1.3. Server Hello
        legacy_tls_ver: ProtoColVersion, // value: u16 == 0x0303
        pub(crate) random: Random,
        // Echo of the contents of 'legacy_session_id' field from client's ClientHello message.
        pub(crate) legacy_session_id: Option<&'a [u8]>,
        // B.4. Cipher Suites. Dance with either AES or CHACHA20!
        // TlsAes128GcmSha256 (0x13, 0x01)
        // TlsAes256GcmSha384 (0x13, 0x02)
        // TLS_CHACHA20_POLY1305_SHA256 (0x13, 0x03)
        pub(crate) cipher_suite: CipherSuite,
        // TLS 1.3 client MUST send a vector [1, 0] for compression methods.
        // The TLS 1.3 server MUST echo the same value.
        legacy_compression_method: u8, // value == 0
        // ServerHello, page 32, sec 4.1.3. Server Hello
        // TLS 1.3 MUST contain the "supported_versions" extension.
        // It may contain either "pre_shared_key" or the "key_share" extension, or both.
        pub(crate) extensions: Vec<Extension<'a>>,
    }

    impl<'a> ServerHelloHandshake<'a> {
        pub fn new(rec_frag_len: u16, random: Random, sid: Option<&'a [u8]>, cipher: CipherSuite, extensions: Vec<Extension<'a>>) -> Self {
            ServerHelloHandshake {
                rct: ContentType::Handshake,
                legacy_rec_ver: LEGACY_VER_0X0303,
                fragment_len: rec_frag_len,
                ht: HandshakeType::ServerHello,
                len: (rec_frag_len - 4) as u32,
                legacy_tls_ver: LEGACY_VER_0X0303,
                random,
                legacy_session_id: sid,
                cipher_suite: cipher,
                legacy_compression_method: 0,
                extensions,
            }
        }

        pub fn serialize() -> Result<Bytes, RecErr> {
            Err(RecErr::BadInput)
        }

        //noinspection ALL
        //noinspection RsMainFunctionNotFound
        pub fn deserialize(bytes: &'a [u8]) -> Result<ServerHelloHandshake<'a>, RecErr> {
            ServerHelloMsgReader::new(bytes)
                .read()
        }
    }

    pub struct ServerHelloMsgReader<'a> {
        i: usize,
        bytes: &'a [u8],
    }

    impl<'a> ServerHelloMsgReader<'a> {
        pub fn new(bytes: &'a [u8]) -> Self {
            Self {
                i: 0,
                bytes,
            }
        }

        fn slide(&mut self, c: usize) {
            debug_assert!(self.i + c <= self.bytes.len(), "ServerHelloMsgReader.slide");
            self.i += c;
        }

        fn peek_u8(&self) -> u8 {
            self.bytes[self.i]
        }

        fn peek_u16(&self) -> u16 {
            ((self.bytes[self.i] as u16) << 8) | (self.bytes[self.i + 1] as u16)
        }

        fn peek_u24(&self) -> usize {
            ((self.bytes[self.i] as usize) << 16) | ((self.bytes[self.i + 1] as usize) << 8) | (self.bytes[self.i + 2] as usize)
        }

        fn read_u8(&mut self) -> u8 {
            (self.peek_u8(), self.slide(1)).0
        }

        fn read_u16(&mut self) -> u16 {
            (self.peek_u16(), self.slide(2)).0
        }

        fn read_u24(&mut self) -> usize {
            (self.peek_u24(), self.slide(3)).0
        }

        fn u8(&mut self, val: u8) -> bool {
            (self.bytes[self.i] == val, self.slide(1)).0
        }

        fn u16(&mut self, val: u16) -> bool {
            (self.peek_u16() == val, self.slide(2)).0
        }

        fn read_bytes(&mut self, n: usize) -> &'a [u8] {
            if n == 0 {
                &[0]
            } else {
                (&self.bytes[self.i..self.i + n], self.slide(n)).0
            }
        }

        fn read_extensions(&mut self) -> Result<Vec<Extension<'a>>, RecErr> {
            // eprintln!("read_extensions i = {}, {:?}", self.i, &self.bytes[self.i..]);
            let (extensions, ext_len) = Extensions::deserialize(&self.bytes[self.i..])?;
            self.slide(ext_len);
            Ok(extensions)
        }

        fn read_empty_compression_methods(&mut self) -> Result<bool, RecErr> {
            if self.read_u8() == 0 {
                Ok(true)
            } else {
                Err(RecErr::CompressionMethods)
            }
        }

        fn read_random(&mut self) -> Result<Random, RecErr> {
            self.read_bytes(32).try_into().map_err(|_| RecErr::RandomVal)
        }

        fn read_session_id(&mut self) -> Option<&'a [u8]> {
            let sid_len: usize = self.read_u8() as usize;
            let sid: &[u8] = self.read_bytes(sid_len);
            if sid_len > 1 {
                Some(sid)
            } else {
                None
            }
        }

        pub fn read(&mut self) -> Result<ServerHelloHandshake<'a>, RecErr> {
            if !self.u8(ContentType::Handshake as u8) {
                return Err(RecErr::RecType)
            }
            if !self.u16(LEGACY_VER_0X0303) {
                return Err(RecErr::LegacyRecordVer)
            }
            let frag_len: usize = self.read_u16() as usize;
            if !(64..=REC_SIZE_BYTES_MAX).contains(&frag_len) {
                return Err(RecErr::FragmentLen)
            }
            if !self.u8(HandshakeType::ServerHello as u8) {
                return Err(RecErr::HandshakeType)
            }
            let msg_len: usize = self.read_u24();
            if !(64..=REC_SIZE_BYTES_MAX).contains(&msg_len) {
                return Err(RecErr::MsgLen)
            }
            assert_eq!(frag_len - 4, msg_len);
            if !self.u16(LEGACY_VER_0X0303) {
                return Err(RecErr::LegacyTLS13MsgVer)
            }
            let random: Random = self.read_random()?;
            let sid = self.read_session_id();
            let cipher_suite = CipherSuites::valid((self.read_u8(), self.read_u8()))?;
            self.read_empty_compression_methods()?;

            let extensions = self.read_extensions()?;

            Ok(ServerHelloHandshake::new((frag_len & 0xFFFF) as u16,
                                         random,
                                         sid,
                                         cipher_suite,
                                         extensions))
        }
    }

    #[repr(u8)]
    #[derive(Clone, Debug)]
    pub enum RecErr {
        RecType = 1,
        LegacyRecordVer = 2,
        FragmentLen = 4,
        LegacyTLS13MsgVer = 7,
        MsgLen = 10,
        RandomVal = 14,
        SessionIdLen = 19,
        CipherSuiteLen = 23,
        CipherUnsupported = 28,
        CipherDuplicate = 31,
        CipherBad = 37,
        CompressionMethods = 41,
        ExtensionLen = 44,
        ExtensionType = 47,
        UnsupportedExtension = 48,
        UnsupportedVersion = 50,
        ExtensionData = 59,

        HandshakeType = 129,
        UnknownAlertDesc = 140,
        TooBig = 251,
        BadInput = 255,
    }
}

// use the following command to run tests defined in the lib, and those in examples.
// RUSTFLAGS="--cfg=release_test -Adead_code -Aunused" cargo test --examples --release -- --show-output
// cargo test --example t3c -- --show-output
#[allow(unused_variables)]
#[cfg(test)]
mod tls13_client_tests {
    use buckle::init_logger;

    use crate::sample;
    use crate::tls3::{CipherSuite, ClientHelloHandshake, Extension};

    #[test]
    fn test_deserialize_01() {
        init_logger(true);
        let random: Vec<u8> = (64..(64 + 32)).collect();
        let res = ClientHelloHandshake::new(random.try_into().unwrap(),
                                            vec![CipherSuite::TlsChacha20Poly1305Sha256, CipherSuite::TlsAes128GcmSha256],
                                            vec![Extension::supported_ver_1_3()]
        );
        assert!(res.is_ok());
        let ch = res.unwrap();
        let mut bytes: [u8; 2048] = [0; 2048];
        let res = ch.serialize(&mut bytes[0..]);
        log::info!("{bytes:?}");
        assert!(res.is_ok());
    }

    // #[test]
    fn test_client_hello() {
        init_logger(true);
        let res = ClientHelloHandshake::deserialize(sample::RAW_CLIENT_HELLO);
        let ch = res.unwrap();
        let mut bytes: [u8; 2048] = [0; 2048];
        let res = ch.serialize(&mut bytes[0..]);
        log::info!("{bytes:?}");
        assert!(res.is_ok());
    }
}

mod sample {
    pub(crate) const RAW_CLIENT_HELLO: &[u8] = &[
        0x16, 0x03, 0x03, 0x00, 0xF8, 0x01, 0x00, 0x00, 0xF4, 0x03, 0x03, 0x00, 0x01, 0x02, 0x03,
        0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F, 0x10, 0x11, 0x12,
        0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1A, 0x1B, 0x1C, 0x1D, 0x1E, 0x1F, 0x20, 0xE0,
        0xE1, 0xE2, 0xE3, 0xE4, 0xE5, 0xE6, 0xE7, 0xE8, 0xE9, 0xEA, 0xEB, 0xEC, 0xED, 0xEE, 0xEF,
        0xF0, 0xF1, 0xF2, 0xF3, 0xF4, 0xF5, 0xF6, 0xF7, 0xF8, 0xF9, 0xFA, 0xFB, 0xFC, 0xFD, 0xFE,
        0xFF, 0x00, 0x08, 0x13, 0x02, 0x13, 0x03, 0x13, 0x01, 0x00, 0xFF, 0x01, 0x00, 0x00, 0xA3,
        0x00, 0x00, 0x00, 0x18, 0x00, 0x16, 0x00, 0x00, 0x13, 0x65, 0x78, 0x61, 0x6D, 0x70, 0x6C,
        0x65, 0x2E, 0x75, 0x6C, 0x66, 0x68, 0x65, 0x69, 0x6D, 0x2E, 0x6E, 0x65, 0x74, 0x00, 0x0B,
        0x00, 0x04, 0x03, 0x00, 0x01, 0x02, 0x00, 0x0A, 0x00, 0x16, 0x00, 0x14, 0x00, 0x1D, 0x00,
        0x17, 0x00, 0x1E, 0x00, 0x19, 0x00, 0x18, 0x01, 0x00, 0x01, 0x01, 0x01, 0x02, 0x01, 0x03,
        0x01, 0x04, 0x00, 0x23, 0x00, 0x00, 0x00, 0x16, 0x00, 0x00, 0x00, 0x17, 0x00, 0x00, 0x00,
        0x0D, 0x00, 0x1E, 0x00, 0x1C, 0x04, 0x03, 0x05, 0x03, 0x06, 0x03, 0x08, 0x07, 0x08, 0x08,
        0x08, 0x09, 0x08, 0x0A, 0x08, 0x0B, 0x08, 0x04, 0x08, 0x05, 0x08, 0x06, 0x04, 0x01, 0x05,
        0x01, 0x06, 0x01, 0x00, 0x2B, 0x00, 0x03, 0x02, 0x03, 0x04, 0x00, 0x2D, 0x00, 0x02, 0x01,
        0x01, 0x00, 0x33, 0x00, 0x26, 0x00, 0x24, 0x00, 0x1D, 0x00, 0x20, 0x35, 0x80, 0x72, 0xD6,
        0x36, 0x58, 0x80, 0xD1, 0xAE, 0xEA, 0x32, 0x9A, 0xDF, 0x91, 0x21, 0x38, 0x38, 0x51, 0xED,
        0x21, 0xA2, 0x8E, 0x3B, 0x75, 0xE9, 0x65, 0xD0, 0xD2, 0xCD, 0x16, 0x62, 0x54, ];
}

// use the following command to run only this example.
// RUSTFLAGS="-Adead_code -Aunused" cargo run --example t3c -- --show-output
#[tokio::main]
async fn main() -> io::Result<()> {
    let tls13_servers = [
        ("www.india.gov", "www.india.gov.in:443"),
        ("usa.gov", "usa.gov:443"),
        ("www.mitre.org", "www.mitre.org:443"),
        ("mozilla.org", "mozilla.org:443"),
        ("letsencrypt.org", "letsencrypt.org:443"),
        ("yourdot.net", "yourdot.net:443"),
        ("github.com", "github.com:443"),
        ("google.com", "google.com:443"),
        ("facebook.com", "facebook.com:443"),
        ("twitter.com", "twitter.com:443"),
        ("microsoft.com", "microsoft.com:443"),
        ("apple.com", "apple.com:443"),
    ];

    let _enc_ch: [u8; 144] = [1, 0, 0, 139, 3, 3, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 0, 0, 6, 19, 3, 19, 1, 19, 2, 1, 0, 0, 93, 0, 0, 0, 18, 0, 16, 0, 0, 13, 119, 119, 119, 46, 105, 110, 100, 105, 97, 46, 103, 111, 118, 0, 43, 0, 3, 2, 3, 4, 0, 10, 0, 6, 0, 4, 0, 29, 0, 23, 0, 13, 0, 8, 0, 6, 8, 7, 4, 3, 8, 4, 0, 51, 0, 38, 0, 36, 0, 29, 0, 32, 53, 128, 114, 214, 54, 88, 128, 209, 174, 234, 50, 154, 223, 145, 33, 56, 56, 81, 237, 33, 162, 142, 59, 117, 233, 101, 208, 210, 205, 22, 98, 84];
    let key_share_data: [u8; 32] = [0x35, 0x80, 0x72, 0xd6, 0x36, 0x58, 0x80, 0xd1, 0xae, 0xea, 0x32, 0x9a, 0xdf, 0x91, 0x21, 0x38, 0x38, 0x51, 0xed, 0x21, 0xa2, 0x8e, 0x3b, 0x75, 0xe9, 0x65, 0xd0, 0xd2, 0xcd, 0x16, 0x62, 0x54];
    init_logger(true);
    for (server_name, server) in tls13_servers {
        log::info!("");
        log::info!("{server}");
        let server_sock_addresses = server.to_socket_addrs()?;
        let mut serv_stream: Option<TcpStream> = None;
        for serv_sock_addr in server_sock_addresses {
            let socket = TcpSocket::new_v4()?;
            if let Ok(sock_stream) = socket.connect(serv_sock_addr).await {
                serv_stream = Some(sock_stream);
                break;
            }
        }
        if let Some(mut tls_stream) = serv_stream {
            tls_stream.writable().await?;

            let random: Vec<u8> = (64..(64 + 32)).collect();
            let res = ClientHelloHandshake::new(random.try_into().unwrap(),
                                                vec![CipherSuite::TlsChacha20Poly1305Sha256,
                                                     CipherSuite::TlsAes128GcmSha256,
                                                     CipherSuite::TlsAes256GcmSha384],
                                                vec![
                                                    Extension::server_name(server_name),
                                                    Extension::supported_ver_1_3(),
                                                    Extension::supported_group_x25519(),
                                                    Extension::signature_algorithm_ed25519(),
                                                    Extension::ed25519_key_share(&key_share_data),
                                                ]
            );
            assert!(res.is_ok());
            let ch = res.unwrap();
            let mut bytes: [u8; 1024] = [0; 1024];
            let ls = ch.serialize(&mut bytes[0..]).unwrap();
            log::info!("{:?}", &bytes[0..ls+1]);
            let res = tls_stream.try_write(&bytes[0..ls]);
            assert!(res.is_ok());
            let n = res.unwrap();
            log::info!("sending {ls} bytes to {server_name}; wrote {n} bytes");

            let mut serv_hello_enc_ext = [0; 8192];
            let mut serv_resp_len: usize = 0;
            let mut ok = true;
            loop {
                tls_stream.readable().await?;
                match tls_stream.try_read(&mut serv_hello_enc_ext[serv_resp_len..]) {
                    Ok(0) => {
                        // log::error!("stream reading complete.");
                        break
                    }
                    Ok(n) => {
                        serv_resp_len += n;
                        // log::info!("[{server:}]: read {n} bytes. total = {serv_resp_len}");
                        continue;
                    }
                    Err(ref e) if e.kind() == io::ErrorKind::WouldBlock => {
                        break;
                    }
                    Err(e) => {
                        ok = false;
                        log::error!("error: {e:#?}");
                        break
                    }
                }
            };
            assert!(ok);
            // log::info!("\tSH response bytes; {:?}", &serv_hello_enc_ext[0..nr]);
            if [0x16, 0x03, 0x03] == serv_hello_enc_ext[0..3] {
                assert_eq!(serv_hello_enc_ext[5], 0x2); // server_hello
                assert_eq!(serv_hello_enc_ext[9..11], [0x3, 0x3]); // legacy_tls_version

                if let Ok(shm) = ServerHelloHandshake::deserialize(&serv_hello_enc_ext) {
                    log::info!("\tSH read {serv_resp_len} bytes; {shm:?}");
                    assert!(shm.legacy_session_id.is_none());
                }
            } else if [0x15, 0x03, 0x03] == serv_hello_enc_ext[0..3] {
                assert_eq!(serv_resp_len, 7);
                // log::info!("\tSH response bytes; {:?}", &serv_hello_enc_ext[0..serv_resp_len]);
                let alert_len = (serv_hello_enc_ext[3] as usize) << 8 | serv_hello_enc_ext[4] as usize;
                assert_eq!(alert_len, serv_resp_len - 5);
                assert!((1u8..=2).contains(&serv_hello_enc_ext[5]));
                let (alert_level, alert_desc) = (serv_hello_enc_ext[5], serv_hello_enc_ext[6]);
                match alert_level {
                    1 => {
                        log::info!("server warning: {}", alert_desc);
                    },
                    2 => {
                        log::info!("server error: {}", alert_desc);
                        match alert_desc.try_into().expect("unknown alert desc!") {
                            AlertDesc::RecordOverflow => log::info!("Error - record overflow."),
                            AlertDesc::HandshakeFailure => log::info!("Error - handshake failure."),
                            AlertDesc::DecodeError => log::info!("Error - client hello message decoding error."),
                            AlertDesc::MissingExtension => log::info!("Error - missing extension."),
                            AlertDesc::UnsupportedExtension => log::info!("Error - unsupported extension."),
                            _ => log::error!("unhandled alert desc!"),
                        }
                    },
                    _ => panic!("unknown alert level and desc: ({alert_level}, {alert_desc})"),
                }
                panic!("client hello fail for {server_name}");
            } else {
                panic!("Fatal Error: No response from {server_name} for client hello! Quitting...");
            }

            tls_stream.shutdown().await?;
        }
    }
    Ok(())
}