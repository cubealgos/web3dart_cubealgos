import 'dart:convert';

import 'package:http/http.dart';
import 'package:web3dart_cubealgos/web3dart_cubealgos.dart';

import 'fee.dart';
import 'fee_history.dart';

export 'fee.dart';
export 'fee_history.dart';

int _currentRequestId = 1;

Future<Map<String, dynamic>> _call(
  String url,
  String method,
  Client client,
  List<Object?> params,
) async {
  final requestPayload = {
    'jsonrpc': '2.0',
    'method': method,
    'params': params,
    'id': _currentRequestId++,
  };

  final response = await client.post(
    Uri.parse(url),
    headers: {'Content-Type': 'application/json'},
    body: jsonEncode(requestPayload),
  );

  final data = jsonDecode(response.body) as Map<String, dynamic>;

  return data;
}

/// Gets a block from the Web3 endpoint.
Future<BlockInformation> getBlockByNumber(
  String url,
  String blockNumber, {
  bool containFullObject = true,
  Client? client,
}) async {
  final c = client ?? Client();
  final data = await _call(url, 'eth_getBlockByNumber', c, [
    blockNumber,
    containFullObject,
  ]);

  final block = BlockInformation.fromJson(data['result']);

  return block;
}

/// Returns fee history of some blocks
Future<FeeHistory> getFeeHistory(
  String url,
  int blockCount,
  String block, {
  List<double>? rewardPercentiles,
  Client? client,
}) async {
  final c = client ?? Client();

  final data = await _call(url, 'eth_feeHistory', c, [
    blockCount,
    block,
    rewardPercentiles,
  ]);

  final history = data['result'];

  final oldestBlock = BigInt.parse(history['oldestBlock'] as String);
  final baseFeePerGas =
      List<String>.from(
        history['baseFeePerGas'],
      ).map((e) => BigInt.parse(e)).toList();
  final reward =
      history['reward'] != null
          ? List.from(history['reward'])
              .map((dynamic e) => List<String>.from(e))
              .map((e) => e.map((e) => BigInt.parse(e)).toList())
              .toList()
          : null;

  final gasUsedRatio =
      List<num>.from(history['gasUsedRatio']).map((e) => e.toDouble()).toList();

  return FeeHistory(baseFeePerGas, oldestBlock, gasUsedRatio, reward);
}

/// Calculates gas and market fees according to EIP-1559.
Future<List<Fee>> getGasInEIP1559(
  String url, {
  List<double> rewardPercentiles = const [25, 50, 75],
  int historicalBlocks = 10,
  String block = 'pending',
}) async {
  final List<Fee> result = [];

  final feeHistory = await getFeeHistory(
    url,
    historicalBlocks,
    block,
    rewardPercentiles: rewardPercentiles,
  );

  final latestBlock = await getBlockByNumber(url, block);
  final baseFee = latestBlock.baseFeePerGas!;

  for (int index = 0; index < rewardPercentiles.length; index++) {
    final List<BigInt> allPriorityFee =
        feeHistory.reward!.map<BigInt>((e) {
          return e[index];
        }).toList();

    final priorityFee = allPriorityFee.reduce(
      (curr, next) => curr > next ? curr : next,
    );

    final estimatedGas = BigInt.from(
      0.9 * baseFee.getInWei.toDouble() + priorityFee.toDouble(),
    );
    final maxFee = BigInt.from(1.5 * estimatedGas.toDouble());

    result.add(
      Fee(
        maxPriorityFeePerGas: priorityFee,
        maxFeePerGas: maxFee,
        estimatedGas: estimatedGas,
      ),
    );
  }

  return result;
}
