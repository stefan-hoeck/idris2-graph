module Test.Main

import Hedgehog
import Test.BitMap

main : IO ()
main = test [ BitMap.props
            ]
