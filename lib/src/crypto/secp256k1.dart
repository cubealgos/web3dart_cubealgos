import 'dart:math';
import 'dart:typed_data';

import 'package:pointycastle/export.dart';
// ignore: implementation_imports
import 'package:pointycastle/src/utils.dart' as utils;

import '../utils/typed_data.dart';
import 'formatting.dart';
import 'keccak.dart';
import 'random_bridge.dart';

final ECDomainParameters params = ECCurve_secp256k1();
final BigInt _halfCurveOrder = params.n >> 1;

/// Generates a public key for the given private key using the ecdsa curve which
/// Ethereum uses.
Uint8List privateKeyBytesToPublic(Uint8List privateKey) {
  return privateKeyToPublic(bytesToUnsignedInt(privateKey));
}

/// Generates a public key for the given private key using the ecdsa curve which
/// Ethereum uses.
Uint8List privateKeyToPublic(BigInt privateKey) {
  final p = (params.G * privateKey)!;

  //skip the type flag, https://github.com/ethereumjs/ethereumjs-util/blob/master/index.js#L319
  return Uint8List.view(p.getEncoded(false).buffer, 1);
}

/// Generates a new private key using the random instance provided. Please make
/// sure you're using a cryptographically secure generator.
BigInt generateNewPrivateKey(Random random) {
  final generator = ECKeyGenerator();

  final keyParams = ECKeyGeneratorParameters(params);

  generator.init(ParametersWithRandom(keyParams, RandomBridge(random)));

  final key = generator.generateKeyPair();
  final privateKey = key.privateKey;
  return privateKey.d!;
}

/// Constructs the Ethereum address associated with the given public key by
/// taking the lower 160 bits of the key's sha3 hash.
Uint8List publicKeyToAddress(Uint8List publicKey) {
  assert(publicKey.length == 64);
  final hashed = keccak256(publicKey);
  assert(hashed.length == 32);
  return hashed.sublist(12, 32);
}

/// Signatures used to sign Ethereum transactions and messages.
class MsgSignature {
  MsgSignature(this.r, this.s, this.v);
  final BigInt r;
  final BigInt s;
  final int v;
}

/// Signs the hashed data in [messageHash] using the given private key.
MsgSignature sign(Uint8List messageHash, Uint8List privateKey) {
  final digest = SHA256Digest();
  final signer = ECDSASigner(null, HMac(digest, 64));
  final key = ECPrivateKey(bytesToUnsignedInt(privateKey), params);

  signer.init(true, PrivateKeyParameter(key));
  var sig = signer.generateSignature(messageHash) as ECSignature;

  /*
	This is necessary because if a message can be signed by (r, s), it can also
	be signed by (r, -s (mod N)) which N being the order of the elliptic function
	used. In order to ensure transactions can't be tampered with (even though it
	would be harmless), Ethereum only accepts the signature with the lower value
	of s to make the signature for the message unique.
	More details at
	https://github.com/web3j/web3j/blob/master/crypto/src/main/java/org/web3j/crypto/ECDSASignature.java#L27
	 */
  if (sig.s.compareTo(_halfCurveOrder) > 0) {
    final canonicalisedS = params.n - sig.s;
    sig = ECSignature(sig.r, canonicalisedS);
  }

  final publicKey = bytesToUnsignedInt(privateKeyBytesToPublic(privateKey));

  final recId = EC.secp256k1.calculateRecoveryId(publicKey, sig, messageHash);

  if (recId == null) {
    throw Exception(
      'Could not construct a recoverable key. This should never happen',
    );
  }

  return MsgSignature(sig.r, sig.s, recId + 27);
}

/// Given an arbitrary message hash and an Ethereum message signature encoded in bytes, returns
/// the public key that was used to sign it.
/// https://github.com/web3j/web3j/blob/c0b7b9c2769a466215d416696021aa75127c2ff1/crypto/src/main/java/org/web3j/crypto/Sign.java#L241
Uint8List ecRecover(Uint8List messageHash, MsgSignature signatureData) {
  final r = padUint8ListTo32(unsignedIntToBytes(signatureData.r));
  final s = padUint8ListTo32(unsignedIntToBytes(signatureData.s));
  assert(r.length == 32);
  assert(s.length == 32);

  final header = signatureData.v & 0xFF;
  // The header byte: 0x1B = first key with even y, 0x1C = first key with odd y,
  //                  0x1D = second key with even y, 0x1E = second key with odd y
  if (header < 27 || header > 34) {
    throw Exception('Header byte out of range: $header');
  }

  final sig = ECSignature(signatureData.r, signatureData.s);

  final recId = header - 27;
  final pubKey = _recoverFromSignature(recId, sig, messageHash, params);
  if (pubKey == null) {
    throw Exception('Could not recover public key from signature');
  }
  return unsignedIntToBytes(pubKey);
}

/// Given an arbitrary message hash, an Ethereum message signature encoded in bytes and
/// a public key encoded in bytes, confirms whether that public key was used to sign
/// the message or not.
bool isValidSignature(
  Uint8List messageHash,
  MsgSignature signatureData,
  Uint8List publicKey,
) {
  final recoveredPublicKey = ecRecover(messageHash, signatureData);
  return bytesToHex(publicKey) == bytesToHex(recoveredPublicKey);
}

/// Given a byte array computes its compressed version and returns it as a byte array,
/// including the leading 02 or 03
Uint8List compressPublicKey(Uint8List compressedPubKey) {
  return Uint8List.view(
    params.curve.decodePoint(compressedPubKey)!.getEncoded(true).buffer,
  );
}

/// Given a byte array computes its expanded version and returns it as a byte array,
/// including the leading 04
Uint8List decompressPublicKey(Uint8List compressedPubKey) {
  return Uint8List.view(
    params.curve.decodePoint(compressedPubKey)!.getEncoded(false).buffer,
  );
}

BigInt? _recoverFromSignature(
  int recId,
  ECSignature sig,
  Uint8List msg,
  ECDomainParameters params,
) {
  final n = params.n;
  final i = BigInt.from(recId ~/ 2);
  final x = sig.r + (i * n);

  //Parameter q of curve
  final prime = BigInt.parse(
    'fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f',
    radix: 16,
  );
  if (x.compareTo(prime) >= 0) return null;

  final R = _decompressKey(x, (recId & 1) == 1, params.curve);
  if (!(R * n)!.isInfinity) return null;

  final e = bytesToUnsignedInt(msg);

  final eInv = (BigInt.zero - e) % n;
  final rInv = sig.r.modInverse(n);
  final srInv = (rInv * sig.s) % n;
  final eInvrInv = (rInv * eInv) % n;

  final q = (params.G * eInvrInv)! + (R * srInv);

  final bytes = q!.getEncoded(false);
  return bytesToUnsignedInt(bytes.sublist(1));
}

ECPoint _decompressKey(BigInt xBN, bool yBit, ECCurve c) {
  List<int> x9IntegerToBytes(BigInt s, int qLength) {
    //https://github.com/bcgit/bc-java/blob/master/core/src/main/java/org/bouncycastle/asn1/x9/X9IntegerConverter.java#L45
    final bytes = intToBytes(s);

    if (qLength < bytes.length) {
      return bytes.sublist(0, bytes.length - qLength);
    } else if (qLength > bytes.length) {
      final tmp = List<int>.filled(qLength, 0);

      final offset = qLength - bytes.length;
      for (var i = 0; i < bytes.length; i++) {
        tmp[i + offset] = bytes[i];
      }

      return tmp;
    }

    return bytes;
  }

  final compEnc = x9IntegerToBytes(xBN, 1 + ((c.fieldSize + 7) ~/ 8));
  compEnc[0] = yBit ? 0x03 : 0x02;
  return c.decodePoint(compEnc)!;
}

/// Elliptic Curve.
class EC {
  const EC._(this._params);

  /// SECP112R1
  static final secp112r1 = EC._(ECCurve_secp112r1());

  /// SECP112R2
  static final secp112r2 = EC._(ECCurve_secp112r2());

  /// SECP128R1
  static final secp128r1 = EC._(ECCurve_secp128r1());

  /// SECP128R2
  static final secp128r2 = EC._(ECCurve_secp128r2());

  /// SECP160K1
  static final secp160k1 = EC._(ECCurve_secp160k1());

  /// SECP160R1
  static final secp160r1 = EC._(ECCurve_secp160r1());

  /// SECP160R2
  static final secp160r2 = EC._(ECCurve_secp160r2());

  /// SECP192K1
  static final secp192k1 = EC._(ECCurve_secp192k1());

  /// SECP192R1
  static final secp192r1 = EC._(ECCurve_secp192r1());

  /// SECP224K1
  static final secp224k1 = EC._(ECCurve_secp224k1());

  /// SECP224R1
  static final secp224r1 = EC._(ECCurve_secp224r1());

  /// SECP256K1
  static final secp256k1 = EC._(ECCurve_secp256k1());

  /// SECP256R1
  static final secp256r1 = EC._(ECCurve_secp256r1());

  /// SECP384R1
  static final secp384r1 = EC._(ECCurve_secp384r1());

  /// SECP521R1
  static final secp521r1 = EC._(ECCurve_secp521r1());

  ///
  static final brainpoolp160r1 = EC._(ECCurve_brainpoolp160r1());

  ///
  static final brainpoolp160t1 = EC._(ECCurve_brainpoolp160t1());

  ///
  static final brainpoolp192r1 = EC._(ECCurve_brainpoolp192r1());

  ///
  static final brainpoolp192t1 = EC._(ECCurve_brainpoolp192t1());

  ///
  static final brainpoolp224r1 = EC._(ECCurve_brainpoolp224r1());

  ///
  static final brainpoolp224t1 = EC._(ECCurve_brainpoolp224t1());

  ///
  static final brainpoolp256r1 = EC._(ECCurve_brainpoolp256r1());

  ///
  static final brainpoolp256t1 = EC._(ECCurve_brainpoolp256t1());

  ///
  static final brainpoolp320r1 = EC._(ECCurve_brainpoolp320r1());

  ///
  static final brainpoolp320t1 = EC._(ECCurve_brainpoolp320t1());

  ///
  static final brainpoolp384r1 = EC._(ECCurve_brainpoolp384r1());

  ///
  static final brainpoolp384t1 = EC._(ECCurve_brainpoolp384t1());

  ///
  static final brainpoolp512r1 = EC._(ECCurve_brainpoolp512r1());

  ///
  static final brainpoolp512t1 = EC._(ECCurve_brainpoolp512t1());

  ///
  static final gostr3410_2001_cryptopro_a = EC._(
    ECCurve_gostr3410_2001_cryptopro_a(),
  );

  ///
  static final gostr3410_2001_cryptopro_b = EC._(
    ECCurve_gostr3410_2001_cryptopro_b(),
  );

  ///
  static final gostr3410_2001_cryptopro_c = EC._(
    ECCurve_gostr3410_2001_cryptopro_c(),
  );

  ///
  static final gostr3410_2001_cryptopro_xcha = EC._(
    ECCurve_gostr3410_2001_cryptopro_xcha(),
  );

  ///
  static final gostr3410_2001_cryptopro_xchb = EC._(
    ECCurve_gostr3410_2001_cryptopro_xchb(),
  );

  ///
  static final prime192v1 = EC._(ECCurve_prime192v1());

  ///
  static final prime192v2 = EC._(ECCurve_prime192v2());

  ///
  static final prime192v3 = EC._(ECCurve_prime192v3());

  ///
  static final prime239v1 = EC._(ECCurve_prime239v1());

  ///
  static final prime239v2 = EC._(ECCurve_prime239v2());

  ///
  static final prime239v3 = EC._(ECCurve_prime239v3());

  ///
  static final prime256v1 = EC._(ECCurve_prime256v1());

  final ECDomainParameters _params;

  /// Creates a Public Key from the given Private Key.
  Uint8List createPublicKey(BigInt privateKey, bool compressed) {
    final q = _params.G * privateKey;

    return q!.getEncoded(compressed);
  }

  /// Creates a Compressed [PublicKey] from the given public key.
  Uint8List compressPublicKey(Uint8List publicKey) {
    final ec = _params.curve.decodePoint(publicKey);
    final compressed = ec!.getEncoded(true);

    return compressed;
  }

  /// Creates a Compressed [PublicKey] from the given public key.
  Uint8List uncompressPublicKey(Uint8List publicKey) {
    final ec = _params.curve.decodePoint(publicKey);
    final compressed = ec!.getEncoded(false);

    return compressed;
  }

  /// Generates a Digital Signature.
  ECSignature generateSignature(
    BigInt privateKey,
    Uint8List message, [
    bool makeCanonical = true,
  ]) {
    var signer = ECDSASigner();

    var priv = PrivateKeyParameter(ECPrivateKey(privateKey, _params));

    final sGen = Random.secure();
    var ran = SecureRandom('Fortuna');
    ran.seed(
      KeyParameter(
        Uint8List.fromList(List.generate(32, (_) => sGen.nextInt(255))),
      ),
    );

    signer.init(true, ParametersWithRandom(priv, ran));
    var rs = signer.generateSignature(message);
    final signature = rs as ECSignature;

    if (makeCanonical) {
      final canonical = signature.normalize(_params);

      return canonical;
    } else {
      return signature;
    }
  }

  /// Verifies a Digital Signature.
  bool verifySignature(
    Uint8List publicKey,
    Uint8List message,
    ECSignature signature,
  ) {
    var signer = ECDSASigner();

    var q = _params.curve.decodePoint(publicKey);
    var pub = PublicKeyParameter(ECPublicKey(q, _params));
    signer.init(false, pub);

    var result = signer.verifySignature(message, signature);
    return result;
  }

  /// Calculates Recovery Id for the Public Key and Message.
  int? calculateRecoveryId(
    BigInt publicKey,
    ECSignature signature,
    Uint8List message,
  ) {
    return calculateRecoveryIdSec(publicKey, signature, message, _params);
  }
}

/// Calculates Recovery Id for the Public Key and Message.
int? calculateRecoveryIdSec(
  BigInt publicKey,
  ECSignature signature,
  Uint8List message,
  ECDomainParameters params,
) {
  for (var i = 0; i < 4; i++) {
    final k = _recoverFromSignatureSec(i, signature, message, params);
    if (k == publicKey) {
      return i;
    }
  }

  return null;
}

BigInt? _recoverFromSignatureSec(
  int recId,
  ECSignature sig,
  Uint8List msg,
  ECDomainParameters params,
) {
  final n = params.n;
  final i = BigInt.from(recId ~/ 2);
  final x = sig.r + (i * n);

  //Parameter q of curve
  final prime = BigInt.parse(
    'fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f',
    radix: 16,
  );
  if (x.compareTo(prime) >= 0) return null;

  final R = _decompressKeySec(x, (recId & 1) == 1, params.curve);
  if (!(R * n)!.isInfinity) return null;

  final e = utils.decodeBigIntWithSign(1, msg);

  final eInv = (BigInt.zero - e) % n;
  final rInv = sig.r.modInverse(n);
  final srInv = (rInv * sig.s) % n;
  final eInvrInv = (rInv * eInv) % n;

  final q = (params.G * eInvrInv)! + (R * srInv);

  final bytes = q!.getEncoded(false);
  return utils.decodeBigIntWithSign(1, bytes.sublist(1));
}

ECPoint _decompressKeySec(BigInt xBN, bool yBit, ECCurve c) {
  List<int> x9IntegerToBytes(BigInt s, int qLength) {
    //https://github.com/bcgit/bc-java/blob/master/core/src/main/java/org/bouncycastle/asn1/x9/X9IntegerConverter.java#L45
    final bytes = utils.encodeBigInt(s);

    if (qLength < bytes.length) {
      return bytes.sublist(0, bytes.length - qLength);
    } else if (qLength > bytes.length) {
      final tmp = List<int>.filled(qLength, 0);

      final offset = qLength - bytes.length;
      for (var i = 0; i < bytes.length; i++) {
        tmp[i + offset] = bytes[i];
      }

      return tmp;
    }

    return bytes;
  }

  final compEnc = x9IntegerToBytes(xBN, 1 + ((c.fieldSize + 7) ~/ 8));
  compEnc[0] = yBit ? 0x03 : 0x02;
  return c.decodePoint(compEnc)!;
}
