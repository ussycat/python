package jp.gr.java_conf.sh.edivoice

import android.os.Bundle
import android.view.LayoutInflater
import android.view.View
import android.view.ViewGroup
import android.widget.TextView
import androidx.appcompat.app.AlertDialog
import androidx.appcompat.app.AppCompatActivity
import androidx.lifecycle.lifecycleScope
import androidx.recyclerview.widget.DividerItemDecoration
import androidx.recyclerview.widget.LinearLayoutManager
import androidx.recyclerview.widget.RecyclerView
import com.google.android.material.textfield.TextInputEditText
import jp.gr.java_conf.sh.edivoice.databinding.ActivityDictionaryBinding
import jp.gr.java_conf.sh.edivoice.databinding.DialogAddWordBinding
import jp.gr.java_conf.sh.edivoice.db.AppDatabase
import jp.gr.java_conf.sh.edivoice.db.DictionaryEntry
import kotlinx.coroutines.Dispatchers
import kotlinx.coroutines.launch
import kotlinx.coroutines.withContext

class DictionaryActivity : AppCompatActivity() {

    private lateinit var binding: ActivityDictionaryBinding
    private lateinit var adapter: DictAdapter
    private val db by lazy { AppDatabase.getInstance(this) }

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        binding = ActivityDictionaryBinding.inflate(layoutInflater)
        setContentView(binding.root)
        setSupportActionBar(binding.toolbar)
        supportActionBar?.setDisplayHomeAsUpEnabled(true)

        adapter = DictAdapter(
            onEdit = { entry -> showEditDialog(entry) },
            onDelete = { entry -> confirmDelete(entry) }
        )

        binding.recyclerView.apply {
            layoutManager = LinearLayoutManager(this@DictionaryActivity)
            addItemDecoration(DividerItemDecoration(context, DividerItemDecoration.VERTICAL))
            adapter = this@DictionaryActivity.adapter
        }

        binding.fabAdd.setOnClickListener { showAddDialog() }

        lifecycleScope.launch {
            db.dictionaryDao().getAll().collect { list ->
                adapter.submitList(list)
                binding.tvEmpty.visibility = if (list.isEmpty()) View.VISIBLE else View.GONE
            }
        }
    }

    override fun onSupportNavigateUp(): Boolean { finish(); return true }

    private fun showAddDialog() = showWordDialog(null)

    private fun showEditDialog(entry: DictionaryEntry) = showWordDialog(entry)

    private fun showWordDialog(existing: DictionaryEntry?) {
        val dialogBinding = DialogAddWordBinding.inflate(LayoutInflater.from(this))
        existing?.let {
            dialogBinding.etFrom.setText(it.fromText)
            dialogBinding.etTo.setText(it.toText)
        }

        AlertDialog.Builder(this)
            .setTitle(if (existing == null) R.string.dict_add_title else R.string.dict_edit_title)
            .setView(dialogBinding.root)
            .setPositiveButton(R.string.dict_save) { _, _ ->
                val from = dialogBinding.etFrom.text?.toString()?.trim() ?: return@setPositiveButton
                val to = dialogBinding.etTo.text?.toString()?.trim() ?: return@setPositiveButton
                if (from.isEmpty() || to.isEmpty()) return@setPositiveButton
                lifecycleScope.launch(Dispatchers.IO) {
                    if (existing == null) {
                        db.dictionaryDao().insert(DictionaryEntry(fromText = from, toText = to))
                    } else {
                        db.dictionaryDao().update(existing.copy(fromText = from, toText = to))
                    }
                }
            }
            .setNegativeButton(R.string.dict_cancel, null)
            .show()
    }

    private fun confirmDelete(entry: DictionaryEntry) {
        AlertDialog.Builder(this)
            .setMessage(R.string.dict_delete_confirm)
            .setPositiveButton("削除") { _, _ ->
                lifecycleScope.launch(Dispatchers.IO) { db.dictionaryDao().delete(entry) }
            }
            .setNegativeButton(R.string.dict_cancel, null)
            .show()
    }

    // ── Adapter ───────────────────────────────────────────────────────────────

    class DictAdapter(
        private val onEdit: (DictionaryEntry) -> Unit,
        private val onDelete: (DictionaryEntry) -> Unit
    ) : RecyclerView.Adapter<DictAdapter.VH>() {

        private var items: List<DictionaryEntry> = emptyList()

        fun submitList(list: List<DictionaryEntry>) {
            items = list
            notifyDataSetChanged()
        }

        override fun onCreateViewHolder(parent: ViewGroup, viewType: Int): VH {
            val v = LayoutInflater.from(parent.context)
                .inflate(R.layout.item_dictionary, parent, false)
            return VH(v)
        }

        override fun onBindViewHolder(holder: VH, position: Int) {
            val entry = items[position]
            holder.tvFrom.text = entry.fromText
            holder.tvTo.text = entry.toText
            holder.btnEdit.setOnClickListener { onEdit(entry) }
            holder.btnDelete.setOnClickListener { onDelete(entry) }
        }

        override fun getItemCount() = items.size

        class VH(view: View) : RecyclerView.ViewHolder(view) {
            val tvFrom: TextView = view.findViewById(R.id.tvFrom)
            val tvTo: TextView = view.findViewById(R.id.tvTo)
            val btnEdit: View = view.findViewById(R.id.btnEdit)
            val btnDelete: View = view.findViewById(R.id.btnDelete)
        }
    }
}
