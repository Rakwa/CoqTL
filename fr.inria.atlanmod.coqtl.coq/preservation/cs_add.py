import unittest
import subprocess as sp
import shutil
import os

# operation: add to child specification

class RegressionTest(unittest.TestCase):

    def setUp(self):
        print("----------------------------------")
        print("In method", self._testMethodName)
        
    def cmd(self, input):
        sp.call(["coq_makefile", "-f", input, "-o", "Makefile"])
        error_code = sp.call(["make"])
        return error_code

    def reset(self):

        # paths
        clean = "./clean/"
        base = "./"
        core = "core"
        examples = "transformations"
        clean_core = os.path.join(clean, core) 
        base_core = os.path.join(base, core)
        clean_examples = os.path.join(clean, examples) 
        base_examples = os.path.join(base, examples)

        # clean
        shutil.rmtree(base_core, ignore_errors=True)
        shutil.rmtree(base_examples, ignore_errors=True)

        # copy
        shutil.copytree(clean_core, base_core, dirs_exist_ok=True)
        shutil.copytree(clean_examples, base_examples, dirs_exist_ok=True)

    def test_cs_add_UPoBS(self):
        # clean up
        self.reset()

        # prepare paths
        change_nature = "./cs/add/"
        id = "UPoBS.coqproj"
        change_in = "core/modeling/ModelingEngine.v"
        base = "./"

        apply_to = os.path.join(base, change_in)
        change = os.path.join(change_nature, change_in)
        _Coqproject_change = os.path.join(change_nature, id)
        _Coqproject = os.path.join(base, id)

        # apply change
        shutil.copy(change, apply_to)
        shutil.copy(_Coqproject_change, base)

        # execute, expect preserved
        msg = self.cmd(_Coqproject)
        self.assertTrue(msg == 0)

    def test_cs_add_UPoCS(self):
        # clean up
        self.reset()

        # prepare paths
        change_nature = "./cs/add/"
        id = "UPoCS.coqproj"
        change_in = "core/modeling/ModelingEngine.v"
        base = "./"

        apply_to = os.path.join(base, change_in)
        change = os.path.join(change_nature, change_in)
        _Coqproject_change = os.path.join(change_nature, id)
        _Coqproject = os.path.join(base, id)
        
        # apply change
        shutil.copy(change, apply_to)
        shutil.copy(_Coqproject_change, base)

        # execute, expect preserved
        msg = self.cmd(_Coqproject)
        self.assertTrue(msg == 0)

    def test_cs_add_BSC(self):
        # clean up
        self.reset()

        # prepare paths
        change_nature = "./cs/add/"
        id = "BSC.coqproj"
        change_in = "core/modeling/ModelingEngine.v"
        base = "./"

        apply_to = os.path.join(base, change_in)
        change = os.path.join(change_nature, change_in)
        _Coqproject_change = os.path.join(change_nature, id)
        _Coqproject = os.path.join(base, id)
        
        # apply change
        shutil.copy(change, apply_to)
        shutil.copy(_Coqproject_change, base)

        # execute, expect preserved
        msg = self.cmd(_Coqproject)
        self.assertTrue(msg == 0)

    def test_cs_add_CSC(self):
        # clean up
        self.reset()

        # prepare paths
        change_nature = "./cs/add/"
        id = "CSC.coqproj"
        change_in = "core/modeling/ModelingEngine.v"
        base = "./"

        apply_to = os.path.join(base, change_in)
        change = os.path.join(change_nature, change_in)
        _Coqproject_change = os.path.join(change_nature, id)
        _Coqproject = os.path.join(base, id)
        
        # apply change
        shutil.copy(change, apply_to)
        shutil.copy(_Coqproject_change, base)

        # execute, expect preserved
        msg = self.cmd(_Coqproject)
        self.assertTrue(msg != 0)

if __name__ == '__main__':
    unittest.main()


