import brownie
from brownie import *

import pytest

"""
    test swap in Curve from token A to token B directly
"""
## @pytest.mark.skip(reason="WETH2CRV")
def test_swap_in_curve(oneE18, weth_whale, weth, crv, pricer, swapexecutor):  
  ## 1e18
  sell_amount = 1 * oneE18

  ## minimum quote for ETH in CRV
  p = 1 * 1000 * oneE18  
  quote = pricer.getCurvePrice('0x8e764bE4288B842791989DB5b8ec067279829809', weth.address, crv.address, sell_amount) 
  assert quote[1] >= p 

  ## swap on chain
  slippageTolerance = 0.95
  weth.transfer(swapexecutor, sell_amount, {'from': weth_whale})
  minOutput = quote[1] * slippageTolerance
  swapexecutor.execSwapCurve(quote[0], sell_amount, weth.address, crv.address, minOutput, swapexecutor.address)
  balInExecutor = crv.balanceOf(swapexecutor)
  assert balInExecutor >= minOutput

"""
    test swap in Uniswap V2 from token A to token B directly
"""
## @pytest.mark.skip(reason="WETH2USDC")
def test_swap_in_univ2(oneE18, weth_whale, weth, usdc, pricer, swapexecutor):  
  ## 1e18
  sell_amount = 1 * oneE18

  ## minimum quote for ETH in USDC(1e6)
  p = 1 * 500 * 1000000  
  quote = pricer.findOptimalSwap(weth.address, usdc.address, sell_amount) 
  assert quote[1] >= p 

  ## swap on chain
  slippageTolerance = 0.95
  weth.transfer(swapexecutor, sell_amount, {'from': weth_whale})
  minOutput = quote[1] * slippageTolerance
  swapexecutor.execSwapUniV2('0x7a250d5630B4cF539739dF2C5dAcb4c659F2488D', sell_amount, [weth.address, usdc.address], minOutput, swapexecutor.address)
  balInExecutor = usdc.balanceOf(swapexecutor)
  assert balInExecutor >= minOutput
  
"""
    test swap in Uniswap V3 from token A to token B via connectorToken C
"""
## @pytest.mark.skip(reason="WBTC2WETH2USDC")
def test_swap_in_univ3(oneE18, wbtc_whale, wbtc, weth, usdc, pricer, swapexecutor):  
  ## 1e8
  sell_amount = 1 * 100000000

  ## minimum quote for WBTC in USDC(1e6)
  p = 1 * 15000 * 1000000  
  quote = pricer.findOptimalSwap(wbtc.address, usdc.address, sell_amount) 
  assert quote[1] >= p 

  ## swap on chain
  slippageTolerance = 0.95
  wbtc.transfer(swapexecutor, sell_amount, {'from': wbtc_whale})
  minOutput = quote[1] * slippageTolerance
  encodedPath = swapexecutor.encodeUniV3TwoHop(wbtc.address, 500, weth.address, 500, usdc.address)
  swapexecutor.execSwapUniV3(sell_amount, wbtc.address, encodedPath, minOutput, swapexecutor.address)
  balInExecutor = usdc.balanceOf(swapexecutor)
  assert balInExecutor >= minOutput
 
"""
    test swap in Balancer V2 from token A to token B via connectorToken C
"""
## @pytest.mark.skip(reason="WBTC2WETH2USDC")
def test_swap_in_balancer_batch(oneE18, wbtc_whale, wbtc, weth, usdc, pricer, swapexecutor):  
  ## 1e8
  sell_amount = 1 * 100000000

  ## minimum quote for WBTC in USDC(1e6)
  p = 1 * 15000 * 1000000  
  quote = pricer.findOptimalSwap(wbtc.address, usdc.address, sell_amount) 
  assert quote[1] >= p 

  ## swap on chain
  slippageTolerance = 0.95
  wbtc.transfer(swapexecutor, sell_amount, {'from': wbtc_whale})
  minOutput = quote[1] * slippageTolerance
  wbtc2WETHPoolId = '0xa6f548df93de924d73be7d25dc02554c6bd66db500020000000000000000000e'
  weth2USDCPoolId = '0x96646936b91d6b9d7d0c47c496afbf3d6ec7b6f8000200000000000000000019'
  swapexecutor.execSwapBalancerV2Batch(wbtc2WETHPoolId, weth2USDCPoolId, sell_amount, wbtc.address, usdc.address, weth.address, minOutput, swapexecutor.address)
  balInExecutor = usdc.balanceOf(swapexecutor)
  assert balInExecutor >= minOutput
 
"""
    test swap in Balancer V2 from token A to token B directly
"""
## @pytest.mark.skip(reason="WETH2USDC")
def test_swap_in_balancer_single(oneE18, weth_whale, weth, usdc, pricer, swapexecutor):  
  ## 1e18
  sell_amount = 1 * oneE18

  ## minimum quote for WETH in USDC(1e6)
  p = 1 * 500 * 1000000  
  quote = pricer.findOptimalSwap(weth.address, usdc.address, sell_amount) 
  assert quote[1] >= p 

  ## swap on chain
  slippageTolerance = 0.95
  weth.transfer(swapexecutor, sell_amount, {'from': weth_whale})
  minOutput = quote[1] * slippageTolerance
  weth2USDCPoolId = '0x96646936b91d6b9d7d0c47c496afbf3d6ec7b6f8000200000000000000000019'
  swapexecutor.execSwapBalancerV2Single(weth2USDCPoolId, sell_amount, weth.address, usdc.address, minOutput, swapexecutor.address)
  balInExecutor = usdc.balanceOf(swapexecutor)
  assert balInExecutor >= minOutput