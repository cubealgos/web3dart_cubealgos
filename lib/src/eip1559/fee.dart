import 'dart:convert';

class Fee {
  /// The constructor.
  const Fee({
    required this.maxPriorityFeePerGas,
    required this.maxFeePerGas,
    required this.estimatedGas,
  });

  /// Creates a [Fee] from JSON data.
  factory Fee.fromJson(Map<String, dynamic> json) {
    final maxPriorityFeePerGas = json['maxPriorityFeePerGas'];
    final maxFeePerGas = json['maxFeePerGas'];
    final estimatedGas = json['estimatedGas'];

    if (maxPriorityFeePerGas == null || maxPriorityFeePerGas is! String) {
      throw Exception();
    }

    if (maxFeePerGas == null || maxFeePerGas is! String) {
      throw Exception();
    }

    if (estimatedGas == null || estimatedGas is! String) {
      throw Exception();
    }

    return Fee(
      maxPriorityFeePerGas: BigInt.parse(maxPriorityFeePerGas),
      maxFeePerGas: BigInt.parse(maxFeePerGas),
      estimatedGas: BigInt.parse(estimatedGas),
    );
  }

  /// Converts the [Fee] object to JSON map.
  Map<String, dynamic> toJson() => {
    'maxPriorityFeePerGas': maxPriorityFeePerGas.toString(),
    'maxFeePerGas': maxFeePerGas.toString(),
    'estimatedGas': estimatedGas.toString(),
  };

  @override
  String toString() {
    return jsonEncode(toJson());
  }

  /// Max priority fee per gas.
  final BigInt maxPriorityFeePerGas;

  /// Max fee per gas.
  final BigInt maxFeePerGas;

  /// Estimated gas.
  final BigInt estimatedGas;
}
