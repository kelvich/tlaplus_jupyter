import os
import nbformat

from nbconvert.preprocessors import ExecutePreprocessor
from unittest import TestCase

class TestNotebook(TestCase):

    @classmethod
    def setUpClass(cls):
        notebook_path = os.path.join(os.path.dirname(__file__), 'testnb.ipynb')
        nb_name, _ = os.path.splitext(os.path.basename(notebook_path))
        dirname = os.path.dirname(notebook_path)

        with open(notebook_path) as f:
            nb = nbformat.read(f, as_version=4)

        proc = ExecutePreprocessor(timeout=600)
        proc.allow_errors = True
        proc.preprocess(nb, {'metadata': {'path': '/'}})

        cls.cells = nb.cells

    def test_expr(self):
        cell = self.cells[0]
        self.assertEqual(cell.execution_count, 1)
        self.assertEqual(cell.outputs[0]['text'], '{<<1, 1>>, <<1, 2>>, <<1, 3>>, <<2, 2>>, <<2, 3>>, <<3, 3>>}')

    def test_module(self):
        cell = self.cells[1]
        self.assertEqual(cell.execution_count, 2)
        self.assertEqual(cell.outputs, [])

    def test_tlc_run(self):
        cell = self.cells[2]
        self.assertEqual(cell.execution_count, 3)
        text = "".join([o.text for o in cell.outputs])
        self.assertTrue('97 states generated' in text)

    def test_expr_error(self):
        cell = self.cells[3]
        self.assertEqual(cell.execution_count, 4)
        text = cell.outputs[0].text
        self.assertTrue('Could not parse ' in text)
