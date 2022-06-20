import brownie
from brownie import *

import pytest

"""
    test BPT pricing
    
    @pytest.fixture
    def bptpricing():
        return BptPricing.deploy({"from": a[0]})
"""
def test_bpt_pricing_bal_eth(weth_whale, weth, bptpricing):  
  
  (_p, _bal1, _bal2, _V) = bptpricing.calculateBpt(True)
  print('Before swap: bptPriceInETH=' + str(_p) + ', fairBal1=' + str(_bal1) + ', fairBal2=' + str(_bal2) + ', invariant=' + str(_V))
      
  ## check bpt pricing against swap manipulation, e.g., swap WETH for BAL to push BAL price much higher
  ## balancer got some limit in one swap: https://dev.balancer.fi/references/error-codes#pools
  ## bal-eth pool: https://etherscan.io/address/0x5c6ee304399dbdb9c8ef030ab642b10820db8f56#code#F6#L36
  sugar_amount = _bal2 * 0.299
  weth.transfer(bptpricing.address, sugar_amount, {'from': weth_whale})
  bptpricing.swapInBpt()
  
  (_pAfter, _bal1After, _bal2After, _VAfter) = bptpricing.calculateBpt(False)
  print('After swap: bptPriceInETH=' + str(_pAfter) + ', fairBal1=' + str(_bal1After) + ', fairBal2=' + str(_bal2After) + ', invariant=' + str(_VAfter))
  
  # check if any serious change after swap
  diff = 0
  if(_pAfter > _p):
     diff = _pAfter - _p
  else:
     diff = _p - _pAfter
  assert (diff / _p) <= 0.001