import 'dart:typed_data';

import 'package:test/test.dart';

import 'package:web3dart_cubealgos/contracts.dart';
import 'package:web3dart_cubealgos/crypto.dart';

import 'package:web3dart_cubealgos/web3dart_cubealgos.dart'
    show LengthTrackingByteSink;

void expectEncodes<T>(AbiType<T> type, T data, String encoded) {
  final buffer = LengthTrackingByteSink();
  type.encode(data, buffer);

  expect(bytesToHex(buffer.asBytes(), include0x: false), encoded);
}

ByteBuffer bufferFromHex(String hex) {
  return hexToBytes(hex).buffer;
}
