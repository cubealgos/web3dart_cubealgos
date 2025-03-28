class FeeHistory {
  /// The constructor.
  const FeeHistory(
    this.baseFeePerGas,
    this.oldestBlock,
    this.gasUsedRatio,
    this.reward,
  );

  /// The oldest [Block] number.
  final BigInt oldestBlock;

  /// Base fee per gas.
  final List<BigInt> baseFeePerGas;

  /// Gas usage ratio.
  final List<double> gasUsedRatio;

  /// Rewards.
  final List<List<BigInt>>? reward;
}
