from copy import deepcopy
from licenseheaders.licenseheaders import merge_configs


class TestMergeConfigs:
    def test_merge_configs01(self):
        tconfig = dict(
            sub1=dict(a=1, b=[1, 2, 3]),
            sub2="x",
            sub3=dict(d=dict(x=1))
        )
        ret = merge_configs(deepcopy(tconfig), dict(sub1=22, sub2="y"))
        assert ret == dict(sub1=22, sub2="y", sub3=dict(d=dict(x=1)))
        ret = merge_configs(deepcopy(tconfig), dict(update_sub1=dict(b="y")))
        assert ret == dict(sub1=dict(a=1, b="y"), sub2="x", sub3=dict(d=dict(x=1)))
        ret = merge_configs(deepcopy(tconfig),
                            dict(update_sub1=dict(b="y"), update_sub3=dict(update_d=dict(x=2, y=3, z=22))))
        assert ret == dict(sub1=dict(a=1, b="y"), sub2="x", sub3=dict(d=dict(x=2, y=3, z=22)))
